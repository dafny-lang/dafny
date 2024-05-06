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
      Dafny.ISequence<Dafny.Rune> _2233___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _2233___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _2233___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2233___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _2234___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _2234___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _2234___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2234___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _2235_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _2235_r);
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
      BigInteger _2236_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _2236_indexInEnv), ((this).dtor_names).Drop((_2236_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _2237_modName;
      _2237_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_2237_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _2238_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _2238_body = _out15;
        s = RAST.Mod.create_Mod(_2237_modName, _2238_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _2239_i = BigInteger.Zero; _2239_i < _hi5; _2239_i++) {
        Dafny.ISequence<RAST._IModDecl> _2240_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source70 = (body).Select(_2239_i);
        if (_source70.is_Module) {
          DAST._IModule _2241___mcc_h0 = _source70.dtor_Module_i_a0;
          DAST._IModule _2242_m = _2241___mcc_h0;
          RAST._IMod _2243_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_2242_m, containingPath);
          _2243_mm = _out16;
          _2240_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_2243_mm));
        } else if (_source70.is_Class) {
          DAST._IClass _2244___mcc_h1 = _source70.dtor_Class_i_a0;
          DAST._IClass _2245_c = _2244___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_2245_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2245_c).dtor_name)));
          _2240_generated = _out17;
        } else if (_source70.is_Trait) {
          DAST._ITrait _2246___mcc_h2 = _source70.dtor_Trait_i_a0;
          DAST._ITrait _2247_t = _2246___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _2248_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_2247_t, containingPath);
          _2248_tt = _out18;
          _2240_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_2248_tt));
        } else if (_source70.is_Newtype) {
          DAST._INewtype _2249___mcc_h3 = _source70.dtor_Newtype_i_a0;
          DAST._INewtype _2250_n = _2249___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_2250_n);
          _2240_generated = _out19;
        } else if (_source70.is_SynonymType) {
          DAST._ISynonymType _2251___mcc_h4 = _source70.dtor_SynonymType_i_a0;
          DAST._ISynonymType _2252_s = _2251___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenSynonymType(_2252_s);
          _2240_generated = _out20;
        } else {
          DAST._IDatatype _2253___mcc_h5 = _source70.dtor_Datatype_i_a0;
          DAST._IDatatype _2254_d = _2253___mcc_h5;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_2254_d);
          _2240_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _2240_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _2255_genTpConstraint;
      _2255_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _2255_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_2255_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _2255_genTpConstraint);
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
        for (BigInteger _2256_tpI = BigInteger.Zero; _2256_tpI < _hi6; _2256_tpI++) {
          DAST._ITypeArgDecl _2257_tp;
          _2257_tp = (@params).Select(_2256_tpI);
          DAST._IType _2258_typeArg;
          RAST._ITypeParamDecl _2259_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_2257_tp, out _out22, out _out23);
          _2258_typeArg = _out22;
          _2259_typeParam = _out23;
          RAST._IType _2260_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_2258_typeArg, false, false);
          _2260_rType = _out24;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2258_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2260_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2259_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2261_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2262_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2263_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2264_whereConstraints;
      Dafny.ISet<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _2261_typeParamsSet = _out25;
      _2262_rTypeParams = _out26;
      _2263_rTypeParamsDecls = _out27;
      _2264_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _2265_constrainedTypeParams;
      _2265_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2263_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _2266_fields;
      _2266_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _2267_fieldInits;
      _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _2268_fieldI = BigInteger.Zero; _2268_fieldI < _hi7; _2268_fieldI++) {
        DAST._IField _2269_field;
        _2269_field = ((c).dtor_fields).Select(_2268_fieldI);
        RAST._IType _2270_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_2269_field).dtor_formal).dtor_typ, false, false);
        _2270_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _2271_fieldRustName;
        _2271_fieldRustName = DCOMP.__default.escapeName(((_2269_field).dtor_formal).dtor_name);
        _2266_fields = Dafny.Sequence<RAST._IField>.Concat(_2266_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_2271_fieldRustName, _2270_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source71 = (_2269_field).dtor_defaultValue;
        if (_source71.is_None) {
          {
            RAST._IExpr _2272_default;
            _2272_default = RAST.__default.std__Default__default;
            _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_2271_fieldRustName, _2272_default)));
          }
        } else {
          DAST._IExpression _2273___mcc_h0 = _source71.dtor_value;
          DAST._IExpression _2274_e = _2273___mcc_h0;
          {
            RAST._IExpr _2275_expr;
            DCOMP._IOwnership _2276___v40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2277___v41;
            RAST._IExpr _out30;
            DCOMP._IOwnership _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            (this).GenExpr(_2274_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
            _2275_expr = _out30;
            _2276___v40 = _out31;
            _2277___v41 = _out32;
            _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_2269_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_2275_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _2278_typeParamI = BigInteger.Zero; _2278_typeParamI < _hi8; _2278_typeParamI++) {
        DAST._IType _2279_typeArg;
        RAST._ITypeParamDecl _2280_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_2278_typeParamI), out _out33, out _out34);
        _2279_typeArg = _out33;
        _2280_typeParam = _out34;
        RAST._IType _2281_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_2279_typeArg, false, false);
        _2281_rTypeArg = _out35;
        _2266_fields = Dafny.Sequence<RAST._IField>.Concat(_2266_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2278_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2281_rTypeArg))))));
        _2267_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2267_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2278_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _2282_datatypeName;
      _2282_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _2283_struct;
      _2283_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2282_datatypeName, _2263_rTypeParamsDecls, RAST.Fields.create_NamedFields(_2266_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_2283_struct));
      Dafny.ISequence<RAST._IImplMember> _2284_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2285_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _2261_typeParamsSet, out _out36, out _out37);
      _2284_implBodyRaw = _out36;
      _2285_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _2286_implBody;
      _2286_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_2282_datatypeName), _2267_fieldInits))))), _2284_implBodyRaw);
      RAST._IImpl _2287_i;
      _2287_i = RAST.Impl.create_Impl(_2263_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), _2264_whereConstraints, _2286_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2287_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _2288_i;
        _2288_i = BigInteger.Zero;
        while ((_2288_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _2289_superClass;
          _2289_superClass = ((c).dtor_superClasses).Select(_2288_i);
          DAST._IType _source72 = _2289_superClass;
          if (_source72.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2290___mcc_h1 = _source72.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2291___mcc_h2 = _source72.dtor_typeArgs;
            DAST._IResolvedType _2292___mcc_h3 = _source72.dtor_resolved;
            DAST._IResolvedType _source73 = _2292___mcc_h3;
            if (_source73.is_Datatype) {
              DAST._IDatatypeType _2293___mcc_h7 = _source73.dtor_datatypeType;
            } else if (_source73.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2294___mcc_h9 = _source73.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _2295___mcc_h10 = _source73.dtor_attributes;
              Dafny.ISequence<DAST._IType> _2296_typeArgs = _2291___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2297_traitPath = _2290___mcc_h1;
              {
                RAST._IType _2298_pathStr;
                RAST._IType _out38;
                _out38 = DCOMP.COMP.GenPath(_2297_traitPath);
                _2298_pathStr = _out38;
                Dafny.ISequence<RAST._IType> _2299_typeArgs;
                Dafny.ISequence<RAST._IType> _out39;
                _out39 = (this).GenTypeArgs(_2296_typeArgs, false, false);
                _2299_typeArgs = _out39;
                Dafny.ISequence<RAST._IImplMember> _2300_body;
                _2300_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_2285_traitBodies).Contains(_2297_traitPath)) {
                  _2300_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_2285_traitBodies,_2297_traitPath);
                }
                RAST._IType _2301_genSelfPath;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPath(path);
                _2301_genSelfPath = _out40;
                RAST._IModDecl _2302_x;
                _2302_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.Type.create_TypeApp(_2298_pathStr, _2299_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_2301_genSelfPath, _2262_rTypeParams)), _2264_whereConstraints, _2300_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_2302_x));
              }
            } else {
              DAST._IType _2303___mcc_h13 = _source73.dtor_baseType;
              DAST._INewtypeRange _2304___mcc_h14 = _source73.dtor_range;
              bool _2305___mcc_h15 = _source73.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _2306___mcc_h16 = _source73.dtor_attributes;
            }
          } else if (_source72.is_Nullable) {
            DAST._IType _2307___mcc_h21 = _source72.dtor_Nullable_i_a0;
          } else if (_source72.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2308___mcc_h23 = _source72.dtor_Tuple_i_a0;
          } else if (_source72.is_Array) {
            DAST._IType _2309___mcc_h25 = _source72.dtor_element;
            BigInteger _2310___mcc_h26 = _source72.dtor_dims;
          } else if (_source72.is_Seq) {
            DAST._IType _2311___mcc_h29 = _source72.dtor_element;
          } else if (_source72.is_Set) {
            DAST._IType _2312___mcc_h31 = _source72.dtor_element;
          } else if (_source72.is_Multiset) {
            DAST._IType _2313___mcc_h33 = _source72.dtor_element;
          } else if (_source72.is_Map) {
            DAST._IType _2314___mcc_h35 = _source72.dtor_key;
            DAST._IType _2315___mcc_h36 = _source72.dtor_value;
          } else if (_source72.is_SetBuilder) {
            DAST._IType _2316___mcc_h39 = _source72.dtor_element;
          } else if (_source72.is_MapBuilder) {
            DAST._IType _2317___mcc_h41 = _source72.dtor_key;
            DAST._IType _2318___mcc_h42 = _source72.dtor_value;
          } else if (_source72.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2319___mcc_h45 = _source72.dtor_args;
            DAST._IType _2320___mcc_h46 = _source72.dtor_result;
          } else if (_source72.is_Primitive) {
            DAST._IPrimitive _2321___mcc_h49 = _source72.dtor_Primitive_i_a0;
          } else if (_source72.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2322___mcc_h51 = _source72.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _2323___mcc_h53 = _source72.dtor_TypeArg_i_a0;
          }
          _2288_i = (_2288_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _2324_d;
      _2324_d = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), _2264_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_2282_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _2325_defaultImpl;
      _2325_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2324_d));
      RAST._IImpl _2326_p;
      _2326_p = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _2327_printImpl;
      _2327_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2326_p));
      RAST._IImpl _2328_pp;
      _2328_pp = RAST.Impl.create_ImplFor(_2263_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2282_datatypeName), _2262_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _2329_ptrPartialEqImpl;
      _2329_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2328_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _2325_defaultImpl), _2327_printImpl), _2329_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _2330_typeParamsSet;
      _2330_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _2331_typeParamDecls;
      _2331_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2332_typeParams;
      _2332_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2333_tpI;
      _2333_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_2333_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _2334_tp;
          _2334_tp = ((t).dtor_typeParams).Select(_2333_tpI);
          DAST._IType _2335_typeArg;
          RAST._ITypeParamDecl _2336_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_2334_tp, out _out41, out _out42);
          _2335_typeArg = _out41;
          _2336_typeParamDecl = _out42;
          _2330_typeParamsSet = Dafny.Set<DAST._IType>.Union(_2330_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2335_typeArg));
          _2331_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2331_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2336_typeParamDecl));
          RAST._IType _2337_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_2335_typeArg, false, false);
          _2337_typeParam = _out43;
          _2332_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2332_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2337_typeParam));
          _2333_tpI = (_2333_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2338_fullPath;
      _2338_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _2339_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2340___v45;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_2338_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_2338_fullPath, (t).dtor_attributes)), _2330_typeParamsSet, out _out44, out _out45);
      _2339_implBody = _out44;
      _2340___v45 = _out45;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_2331_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2332_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2339_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2341_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2342_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2343_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2344_whereConstraints;
      Dafny.ISet<DAST._IType> _out46;
      Dafny.ISequence<RAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParamDecl> _out48;
      Dafny.ISequence<Dafny.Rune> _out49;
      (this).GenTypeParameters((c).dtor_typeParams, out _out46, out _out47, out _out48, out _out49);
      _2341_typeParamsSet = _out46;
      _2342_rTypeParams = _out47;
      _2343_rTypeParamsDecls = _out48;
      _2344_whereConstraints = _out49;
      Dafny.ISequence<Dafny.Rune> _2345_constrainedTypeParams;
      _2345_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2343_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _2346_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source74 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source74.is_None) {
        RAST._IType _out50;
        _out50 = (this).GenType((c).dtor_base, false, false);
        _2346_underlyingType = _out50;
      } else {
        RAST._IType _2347___mcc_h0 = _source74.dtor_value;
        RAST._IType _2348_v = _2347___mcc_h0;
        _2346_underlyingType = _2348_v;
      }
      DAST._IType _2349_resultingType;
      _2349_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _2350_datatypeName;
      _2350_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _2350_datatypeName, _2343_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _2346_underlyingType))))));
      RAST._IExpr _2351_fnBody;
      _2351_fnBody = RAST.Expr.create_Identifier(_2350_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source75 = (c).dtor_witnessExpr;
      if (_source75.is_None) {
        {
          _2351_fnBody = (_2351_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      } else {
        DAST._IExpression _2352___mcc_h1 = _source75.dtor_value;
        DAST._IExpression _2353_e = _2352___mcc_h1;
        {
          DAST._IExpression _2354_e;
          _2354_e = ((object.Equals((c).dtor_base, _2349_resultingType)) ? (_2353_e) : (DAST.Expression.create_Convert(_2353_e, (c).dtor_base, _2349_resultingType)));
          RAST._IExpr _2355_eStr;
          DCOMP._IOwnership _2356___v46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2357___v47;
          RAST._IExpr _out51;
          DCOMP._IOwnership _out52;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
          (this).GenExpr(_2354_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out51, out _out52, out _out53);
          _2355_eStr = _out51;
          _2356___v46 = _out52;
          _2357___v47 = _out53;
          _2351_fnBody = (_2351_fnBody).Apply1(_2355_eStr);
        }
      }
      RAST._IImplMember _2358_body;
      _2358_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2351_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), _2344_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_2358_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2343_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2350_datatypeName), _2342_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_2346_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2359_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2360_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2361_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2362_whereConstraints;
      Dafny.ISet<DAST._IType> _out54;
      Dafny.ISequence<RAST._IType> _out55;
      Dafny.ISequence<RAST._ITypeParamDecl> _out56;
      Dafny.ISequence<Dafny.Rune> _out57;
      (this).GenTypeParameters((c).dtor_typeParams, out _out54, out _out55, out _out56, out _out57);
      _2359_typeParamsSet = _out54;
      _2360_rTypeParams = _out55;
      _2361_rTypeParamsDecls = _out56;
      _2362_whereConstraints = _out57;
      Dafny.ISequence<Dafny.Rune> _2363_constrainedTypeParams;
      _2363_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2361_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _2364_synonymTypeName;
      _2364_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _2365_resultingType;
      RAST._IType _out58;
      _out58 = (this).GenType((c).dtor_base, false, false);
      _2365_resultingType = _out58;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2364_synonymTypeName, _2361_rTypeParamsDecls, _2365_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source76 = (c).dtor_witnessExpr;
      if (_source76.is_None) {
      } else {
        DAST._IExpression _2366___mcc_h0 = _source76.dtor_value;
        DAST._IExpression _2367_e = _2366___mcc_h0;
        {
          RAST._IExpr _2368_rStmts;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2369___v48;
          DCOMP._IEnvironment _2370_newEnv;
          RAST._IExpr _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          DCOMP._IEnvironment _out61;
          (this).GenStmts((c).dtor_witnessStmts, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out59, out _out60, out _out61);
          _2368_rStmts = _out59;
          _2369___v48 = _out60;
          _2370_newEnv = _out61;
          RAST._IExpr _2371_rExpr;
          DCOMP._IOwnership _2372___v49;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2373___v50;
          RAST._IExpr _out62;
          DCOMP._IOwnership _out63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
          (this).GenExpr(_2367_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), _2370_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out62, out _out63, out _out64);
          _2371_rExpr = _out62;
          _2372___v49 = _out63;
          _2373___v50 = _out64;
          Dafny.ISequence<Dafny.Rune> _2374_constantName;
          _2374_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_2374_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2365_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_2368_rStmts).Then(_2371_rExpr)))))));
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2375_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2376_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2377_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2378_whereConstraints;
      Dafny.ISet<DAST._IType> _out65;
      Dafny.ISequence<RAST._IType> _out66;
      Dafny.ISequence<RAST._ITypeParamDecl> _out67;
      Dafny.ISequence<Dafny.Rune> _out68;
      (this).GenTypeParameters((c).dtor_typeParams, out _out65, out _out66, out _out67, out _out68);
      _2375_typeParamsSet = _out65;
      _2376_rTypeParams = _out66;
      _2377_rTypeParamsDecls = _out67;
      _2378_whereConstraints = _out68;
      Dafny.ISequence<Dafny.Rune> _2379_datatypeName;
      _2379_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _2380_ctors;
      _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2381_i = BigInteger.Zero; _2381_i < _hi9; _2381_i++) {
        DAST._IDatatypeCtor _2382_ctor;
        _2382_ctor = ((c).dtor_ctors).Select(_2381_i);
        Dafny.ISequence<RAST._IField> _2383_ctorArgs;
        _2383_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        BigInteger _hi10 = new BigInteger(((_2382_ctor).dtor_args).Count);
        for (BigInteger _2384_j = BigInteger.Zero; _2384_j < _hi10; _2384_j++) {
          DAST._IFormal _2385_formal;
          _2385_formal = ((_2382_ctor).dtor_args).Select(_2384_j);
          RAST._IType _2386_formalType;
          RAST._IType _out69;
          _out69 = (this).GenType((_2385_formal).dtor_typ, false, false);
          _2386_formalType = _out69;
          if ((c).dtor_isCo) {
            _2383_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2383_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2385_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_2386_formalType))))));
          } else {
            _2383_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2383_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2385_formal).dtor_name), _2386_formalType))));
          }
        }
        _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2380_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_2382_ctor).dtor_name), RAST.Fields.create_NamedFields(_2383_ctorArgs))));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2387_selfPath;
      _2387_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _2388_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2389_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out70;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out71;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_2387_selfPath, (c).dtor_attributes))), _2375_typeParamsSet, out _out70, out _out71);
      _2388_implBodyRaw = _out70;
      _2389_traitBodies = _out71;
      Dafny.ISequence<RAST._IImplMember> _2390_implBody;
      _2390_implBody = _2388_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2391_emittedFields;
      _2391_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2392_i = BigInteger.Zero; _2392_i < _hi11; _2392_i++) {
        DAST._IDatatypeCtor _2393_ctor;
        _2393_ctor = ((c).dtor_ctors).Select(_2392_i);
        BigInteger _hi12 = new BigInteger(((_2393_ctor).dtor_args).Count);
        for (BigInteger _2394_j = BigInteger.Zero; _2394_j < _hi12; _2394_j++) {
          DAST._IFormal _2395_formal;
          _2395_formal = ((_2393_ctor).dtor_args).Select(_2394_j);
          if (!((_2391_emittedFields).Contains((_2395_formal).dtor_name))) {
            _2391_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2391_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2395_formal).dtor_name));
            RAST._IType _2396_formalType;
            RAST._IType _out72;
            _out72 = (this).GenType((_2395_formal).dtor_typ, false, false);
            _2396_formalType = _out72;
            Dafny.ISequence<RAST._IMatchCase> _2397_cases;
            _2397_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _2398_k = BigInteger.Zero; _2398_k < _hi13; _2398_k++) {
              DAST._IDatatypeCtor _2399_ctor2;
              _2399_ctor2 = ((c).dtor_ctors).Select(_2398_k);
              Dafny.ISequence<Dafny.Rune> _2400_pattern;
              _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_2399_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _2401_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              bool _2402_hasMatchingField;
              _2402_hasMatchingField = false;
              BigInteger _hi14 = new BigInteger(((_2399_ctor2).dtor_args).Count);
              for (BigInteger _2403_l = BigInteger.Zero; _2403_l < _hi14; _2403_l++) {
                DAST._IFormal _2404_formal2;
                _2404_formal2 = ((_2399_ctor2).dtor_args).Select(_2403_l);
                if (object.Equals((_2395_formal).dtor_name, (_2404_formal2).dtor_name)) {
                  _2402_hasMatchingField = true;
                }
                _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2400_pattern, DCOMP.__default.escapeName((_2404_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2400_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_2400_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_2402_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _2401_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeName((_2395_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _2401_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2395_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _2401_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _2405_ctorMatch;
              _2405_ctorMatch = RAST.MatchCase.create(_2400_pattern, RAST.Expr.create_RawExpr(_2401_rhs));
              _2397_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2397_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_2405_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _2397_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2397_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _2406_methodBody;
            _2406_methodBody = RAST.Expr.create_Match(RAST.__default.self, _2397_cases);
            _2390_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_2390_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeName((_2395_formal).dtor_name), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_2396_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2406_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _2407_types;
        _2407_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _2408_typeI = BigInteger.Zero; _2408_typeI < _hi15; _2408_typeI++) {
          DAST._IType _2409_typeArg;
          RAST._ITypeParamDecl _2410_rTypeParamDecl;
          DAST._IType _out73;
          RAST._ITypeParamDecl _out74;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_2408_typeI), out _out73, out _out74);
          _2409_typeArg = _out73;
          _2410_rTypeParamDecl = _out74;
          RAST._IType _2411_rTypeArg;
          RAST._IType _out75;
          _out75 = (this).GenType(_2409_typeArg, false, false);
          _2411_rTypeArg = _out75;
          _2407_types = Dafny.Sequence<RAST._IType>.Concat(_2407_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2411_rTypeArg))));
        }
        _2380_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2380_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_2412_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _2412_tpe);
})), _2407_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _2413_enumBody;
      _2413_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _2379_datatypeName, _2377_rTypeParamsDecls, _2380_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2377_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), _2378_whereConstraints, _2390_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _2414_printImplBodyCases;
      _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2415_i = BigInteger.Zero; _2415_i < _hi16; _2415_i++) {
        DAST._IDatatypeCtor _2416_ctor;
        _2416_ctor = ((c).dtor_ctors).Select(_2415_i);
        Dafny.ISequence<Dafny.Rune> _2417_ctorMatch;
        _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2416_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _2418_modulePrefix;
        _2418_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName(((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _2419_printRhs;
        _2419_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _2418_modulePrefix), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((_2416_ctor).dtor_name)), (((_2416_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _hi17 = new BigInteger(((_2416_ctor).dtor_args).Count);
        for (BigInteger _2420_j = BigInteger.Zero; _2420_j < _hi17; _2420_j++) {
          DAST._IFormal _2421_formal;
          _2421_formal = ((_2416_ctor).dtor_args).Select(_2420_j);
          Dafny.ISequence<Dafny.Rune> _2422_formalName;
          _2422_formalName = DCOMP.__default.escapeName((_2421_formal).dtor_name);
          _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2417_ctorMatch, _2422_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_2420_j).Sign == 1) {
            _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeName((_2421_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        _2417_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_2417_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_2416_ctor).dtor_hasAnyArgs) {
          _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _2419_printRhs = (_2419_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2414_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2417_ctorMatch), RAST.Expr.create_Block(_2419_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _2414_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2414_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2379_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2423_defaultConstrainedTypeParams;
      _2423_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2377_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _2424_printImplBody;
      _2424_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _2414_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _2425_printImpl;
      _2425_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2377_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2377_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2424_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _2426_defaultImpl;
      _2426_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _2427_structName;
        _2427_structName = (RAST.Expr.create_Identifier(_2379_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _2428_structAssignments;
        _2428_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _2429_i = BigInteger.Zero; _2429_i < _hi18; _2429_i++) {
          DAST._IFormal _2430_formal;
          _2430_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_2429_i);
          _2428_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2428_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName((_2430_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _2431_defaultConstrainedTypeParams;
        _2431_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2377_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _2432_fullType;
        _2432_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2379_datatypeName), _2376_rTypeParams);
        _2426_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2431_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _2432_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2432_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_2427_structName, _2428_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_2413_enumBody, _2425_printImpl), _2426_defaultImpl);
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
        for (BigInteger _2433_i = BigInteger.Zero; _2433_i < _hi19; _2433_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2433_i))));
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
        for (BigInteger _2434_i = BigInteger.Zero; _2434_i < _hi20; _2434_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2434_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _2435_i;
        _2435_i = BigInteger.Zero;
        while ((_2435_i) < (new BigInteger((args).Count))) {
          RAST._IType _2436_genTp;
          RAST._IType _out76;
          _out76 = (this).GenType((args).Select(_2435_i), inBinding, inFn);
          _2436_genTp = _out76;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_2436_genTp));
          _2435_i = (_2435_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source77 = c;
      if (_source77.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2437___mcc_h0 = _source77.dtor_Path_i_a0;
        Dafny.ISequence<DAST._IType> _2438___mcc_h1 = _source77.dtor_typeArgs;
        DAST._IResolvedType _2439___mcc_h2 = _source77.dtor_resolved;
        DAST._IResolvedType _2440_resolved = _2439___mcc_h2;
        Dafny.ISequence<DAST._IType> _2441_args = _2438___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2442_p = _2437___mcc_h0;
        {
          RAST._IType _2443_t;
          RAST._IType _out77;
          _out77 = DCOMP.COMP.GenPath(_2442_p);
          _2443_t = _out77;
          Dafny.ISequence<RAST._IType> _2444_typeArgs;
          Dafny.ISequence<RAST._IType> _out78;
          _out78 = (this).GenTypeArgs(_2441_args, inBinding, inFn);
          _2444_typeArgs = _out78;
          s = RAST.Type.create_TypeApp(_2443_t, _2444_typeArgs);
          DAST._IResolvedType _source78 = _2440_resolved;
          if (_source78.is_Datatype) {
            DAST._IDatatypeType _2445___mcc_h21 = _source78.dtor_datatypeType;
            DAST._IDatatypeType _source79 = _2445___mcc_h21;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2446___mcc_h22 = _source79.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2447___mcc_h23 = _source79.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2448_attributes = _2447___mcc_h23;
          } else if (_source78.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2449___mcc_h24 = _source78.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2450___mcc_h25 = _source78.dtor_attributes;
            {
              if ((_2442_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            DAST._IType _2451___mcc_h26 = _source78.dtor_baseType;
            DAST._INewtypeRange _2452___mcc_h27 = _source78.dtor_range;
            bool _2453___mcc_h28 = _source78.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _2454___mcc_h29 = _source78.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2455_attributes = _2454___mcc_h29;
            bool _2456_erased = _2453___mcc_h28;
            DAST._INewtypeRange _2457_range = _2452___mcc_h27;
            DAST._IType _2458_t = _2451___mcc_h26;
            {
              if (_2456_erased) {
                Std.Wrappers._IOption<RAST._IType> _source80 = DCOMP.COMP.NewtypeToRustType(_2458_t, _2457_range);
                if (_source80.is_None) {
                } else {
                  RAST._IType _2459___mcc_h30 = _source80.dtor_value;
                  RAST._IType _2460_v = _2459___mcc_h30;
                  s = _2460_v;
                }
              }
            }
          }
        }
      } else if (_source77.is_Nullable) {
        DAST._IType _2461___mcc_h3 = _source77.dtor_Nullable_i_a0;
        DAST._IType _2462_inner = _2461___mcc_h3;
        {
          RAST._IType _2463_innerExpr;
          RAST._IType _out79;
          _out79 = (this).GenType(_2462_inner, inBinding, inFn);
          _2463_innerExpr = _out79;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_2463_innerExpr));
        }
      } else if (_source77.is_Tuple) {
        Dafny.ISequence<DAST._IType> _2464___mcc_h4 = _source77.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IType> _2465_types = _2464___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _2466_args;
          _2466_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2467_i;
          _2467_i = BigInteger.Zero;
          while ((_2467_i) < (new BigInteger((_2465_types).Count))) {
            RAST._IType _2468_generated;
            RAST._IType _out80;
            _out80 = (this).GenType((_2465_types).Select(_2467_i), inBinding, inFn);
            _2468_generated = _out80;
            _2466_args = Dafny.Sequence<RAST._IType>.Concat(_2466_args, Dafny.Sequence<RAST._IType>.FromElements(_2468_generated));
            _2467_i = (_2467_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_2466_args);
        }
      } else if (_source77.is_Array) {
        DAST._IType _2469___mcc_h5 = _source77.dtor_element;
        BigInteger _2470___mcc_h6 = _source77.dtor_dims;
        BigInteger _2471_dims = _2470___mcc_h6;
        DAST._IType _2472_element = _2469___mcc_h5;
        {
          RAST._IType _2473_elem;
          RAST._IType _out81;
          _out81 = (this).GenType(_2472_element, inBinding, inFn);
          _2473_elem = _out81;
          s = _2473_elem;
          BigInteger _2474_i;
          _2474_i = BigInteger.Zero;
          while ((_2474_i) < (_2471_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _2474_i = (_2474_i) + (BigInteger.One);
          }
        }
      } else if (_source77.is_Seq) {
        DAST._IType _2475___mcc_h7 = _source77.dtor_element;
        DAST._IType _2476_element = _2475___mcc_h7;
        {
          RAST._IType _2477_elem;
          RAST._IType _out82;
          _out82 = (this).GenType(_2476_element, inBinding, inFn);
          _2477_elem = _out82;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_2477_elem));
        }
      } else if (_source77.is_Set) {
        DAST._IType _2478___mcc_h8 = _source77.dtor_element;
        DAST._IType _2479_element = _2478___mcc_h8;
        {
          RAST._IType _2480_elem;
          RAST._IType _out83;
          _out83 = (this).GenType(_2479_element, inBinding, inFn);
          _2480_elem = _out83;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_2480_elem));
        }
      } else if (_source77.is_Multiset) {
        DAST._IType _2481___mcc_h9 = _source77.dtor_element;
        DAST._IType _2482_element = _2481___mcc_h9;
        {
          RAST._IType _2483_elem;
          RAST._IType _out84;
          _out84 = (this).GenType(_2482_element, inBinding, inFn);
          _2483_elem = _out84;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_2483_elem));
        }
      } else if (_source77.is_Map) {
        DAST._IType _2484___mcc_h10 = _source77.dtor_key;
        DAST._IType _2485___mcc_h11 = _source77.dtor_value;
        DAST._IType _2486_value = _2485___mcc_h11;
        DAST._IType _2487_key = _2484___mcc_h10;
        {
          RAST._IType _2488_keyType;
          RAST._IType _out85;
          _out85 = (this).GenType(_2487_key, inBinding, inFn);
          _2488_keyType = _out85;
          RAST._IType _2489_valueType;
          RAST._IType _out86;
          _out86 = (this).GenType(_2486_value, inBinding, inFn);
          _2489_valueType = _out86;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_2488_keyType, _2489_valueType));
        }
      } else if (_source77.is_SetBuilder) {
        DAST._IType _2490___mcc_h12 = _source77.dtor_element;
        DAST._IType _2491_elem = _2490___mcc_h12;
        {
          RAST._IType _2492_elemType;
          RAST._IType _out87;
          _out87 = (this).GenType(_2491_elem, inBinding, inFn);
          _2492_elemType = _out87;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2492_elemType));
        }
      } else if (_source77.is_MapBuilder) {
        DAST._IType _2493___mcc_h13 = _source77.dtor_key;
        DAST._IType _2494___mcc_h14 = _source77.dtor_value;
        DAST._IType _2495_value = _2494___mcc_h14;
        DAST._IType _2496_key = _2493___mcc_h13;
        {
          RAST._IType _2497_keyType;
          RAST._IType _out88;
          _out88 = (this).GenType(_2496_key, inBinding, inFn);
          _2497_keyType = _out88;
          RAST._IType _2498_valueType;
          RAST._IType _out89;
          _out89 = (this).GenType(_2495_value, inBinding, inFn);
          _2498_valueType = _out89;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2497_keyType, _2498_valueType));
        }
      } else if (_source77.is_Arrow) {
        Dafny.ISequence<DAST._IType> _2499___mcc_h15 = _source77.dtor_args;
        DAST._IType _2500___mcc_h16 = _source77.dtor_result;
        DAST._IType _2501_result = _2500___mcc_h16;
        Dafny.ISequence<DAST._IType> _2502_args = _2499___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _2503_argTypes;
          _2503_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2504_i;
          _2504_i = BigInteger.Zero;
          while ((_2504_i) < (new BigInteger((_2502_args).Count))) {
            RAST._IType _2505_generated;
            RAST._IType _out90;
            _out90 = (this).GenType((_2502_args).Select(_2504_i), inBinding, true);
            _2505_generated = _out90;
            _2503_argTypes = Dafny.Sequence<RAST._IType>.Concat(_2503_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_2505_generated)));
            _2504_i = (_2504_i) + (BigInteger.One);
          }
          RAST._IType _2506_resultType;
          RAST._IType _out91;
          _out91 = (this).GenType(_2501_result, inBinding, (inFn) || (inBinding));
          _2506_resultType = _out91;
          s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_2503_argTypes, _2506_resultType)));
        }
      } else if (_source77.is_Primitive) {
        DAST._IPrimitive _2507___mcc_h17 = _source77.dtor_Primitive_i_a0;
        DAST._IPrimitive _2508_p = _2507___mcc_h17;
        {
          DAST._IPrimitive _source81 = _2508_p;
          if (_source81.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source81.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source81.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source81.is_Bool) {
            s = RAST.Type.create_Bool();
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source77.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _2509___mcc_h18 = _source77.dtor_Passthrough_i_a0;
        Dafny.ISequence<Dafny.Rune> _2510_v = _2509___mcc_h18;
        s = RAST.__default.RawType(_2510_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _2511___mcc_h19 = _source77.dtor_TypeArg_i_a0;
        Dafny.ISequence<Dafny.Rune> _source82 = _2511___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _2512___mcc_h20 = _source82;
        Dafny.ISequence<Dafny.Rune> _2513_name = _2512___mcc_h20;
        s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_2513_name));
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
      for (BigInteger _2514_i = BigInteger.Zero; _2514_i < _hi21; _2514_i++) {
        DAST._IMethod _source83 = (body).Select(_2514_i);
        DAST._IMethod _2515___mcc_h0 = _source83;
        DAST._IMethod _2516_m = _2515___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source84 = (_2516_m).dtor_overridingPath;
          if (_source84.is_None) {
            {
              RAST._IImplMember _2517_generated;
              RAST._IImplMember _out92;
              _out92 = (this).GenMethod(_2516_m, forTrait, enclosingType, enclosingTypeParams);
              _2517_generated = _out92;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_2517_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2518___mcc_h1 = _source84.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2519_p = _2518___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _2520_existing;
              _2520_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_2519_p)) {
                _2520_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2519_p);
              }
              RAST._IImplMember _2521_genMethod;
              RAST._IImplMember _out93;
              _out93 = (this).GenMethod(_2516_m, true, enclosingType, enclosingTypeParams);
              _2521_genMethod = _out93;
              _2520_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_2520_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_2521_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2519_p, _2520_existing)));
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
      for (BigInteger _2522_i = BigInteger.Zero; _2522_i < _hi22; _2522_i++) {
        DAST._IFormal _2523_param;
        _2523_param = (@params).Select(_2522_i);
        RAST._IType _2524_paramType;
        RAST._IType _out94;
        _out94 = (this).GenType((_2523_param).dtor_typ, false, false);
        _2524_paramType = _out94;
        if ((!((_2524_paramType).CanReadWithoutClone())) && (!((_2523_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2524_paramType = RAST.Type.create_Borrowed(_2524_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_2523_param).dtor_name), _2524_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _2525_params;
      Dafny.ISequence<RAST._IFormal> _out95;
      _out95 = (this).GenParams((m).dtor_params);
      _2525_params = _out95;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2526_paramNames;
      _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2527_paramTypes;
      _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _2528_paramI = BigInteger.Zero; _2528_paramI < _hi23; _2528_paramI++) {
        DAST._IFormal _2529_dafny__formal;
        _2529_dafny__formal = ((m).dtor_params).Select(_2528_paramI);
        RAST._IFormal _2530_formal;
        _2530_formal = (_2525_params).Select(_2528_paramI);
        Dafny.ISequence<Dafny.Rune> _2531_name;
        _2531_name = (_2530_formal).dtor_name;
        _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2526_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2531_name));
        _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2527_paramTypes, _2531_name, (_2530_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _2532_fnName;
      _2532_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2533_selfIdentifier;
      _2533_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _2534_selfId;
        _2534_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_2532_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _2534_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _2535_selfFormal;
          _2535_selfFormal = RAST.Formal.selfBorrowedMut;
          _2525_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_2535_selfFormal), _2525_params);
        } else {
          RAST._IType _2536_tpe;
          RAST._IType _out96;
          _out96 = (this).GenType(enclosingType, false, false);
          _2536_tpe = _out96;
          if (!((_2536_tpe).CanReadWithoutClone())) {
            _2536_tpe = RAST.Type.create_Borrowed(_2536_tpe);
          }
          _2525_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_2534_selfId, _2536_tpe)), _2525_params);
        }
        _2533_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2534_selfId);
      }
      Dafny.ISequence<RAST._IType> _2537_retTypeArgs;
      _2537_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2538_typeI;
      _2538_typeI = BigInteger.Zero;
      while ((_2538_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _2539_typeExpr;
        RAST._IType _out97;
        _out97 = (this).GenType(((m).dtor_outTypes).Select(_2538_typeI), false, false);
        _2539_typeExpr = _out97;
        _2537_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2537_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2539_typeExpr));
        _2538_typeI = (_2538_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _2540_visibility;
      _2540_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _2541_typeParamsFiltered;
      _2541_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _2542_typeParamI = BigInteger.Zero; _2542_typeParamI < _hi24; _2542_typeParamI++) {
        DAST._ITypeArgDecl _2543_typeParam;
        _2543_typeParam = ((m).dtor_typeParams).Select(_2542_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_2543_typeParam).dtor_name)))) {
          _2541_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_2541_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_2543_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2544_typeParams;
      _2544_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_2541_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_2541_typeParamsFiltered).Count);
        for (BigInteger _2545_i = BigInteger.Zero; _2545_i < _hi25; _2545_i++) {
          DAST._IType _2546_typeArg;
          RAST._ITypeParamDecl _2547_rTypeParamDecl;
          DAST._IType _out98;
          RAST._ITypeParamDecl _out99;
          (this).GenTypeParam((_2541_typeParamsFiltered).Select(_2545_i), out _out98, out _out99);
          _2546_typeArg = _out98;
          _2547_rTypeParamDecl = _out99;
          _2544_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2544_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2547_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _2549_env = DCOMP.Environment.Default();
      RAST._IExpr _2550_preBody;
      _2550_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _2551_earlyReturn;
        _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source85 = (m).dtor_outVars;
        if (_source85.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2552___mcc_h0 = _source85.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2553_outVars = _2552___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _2554_tupleArgs;
            _2554_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi26 = new BigInteger((_2553_outVars).Count);
            for (BigInteger _2555_outI = BigInteger.Zero; _2555_outI < _hi26; _2555_outI++) {
              Dafny.ISequence<Dafny.Rune> _2556_outVar;
              _2556_outVar = (_2553_outVars).Select(_2555_outI);
              RAST._IType _2557_outType;
              RAST._IType _out100;
              _out100 = (this).GenType(((m).dtor_outTypes).Select(_2555_outI), false, false);
              _2557_outType = _out100;
              Dafny.ISequence<Dafny.Rune> _2558_outName;
              _2558_outName = DCOMP.__default.escapeName((_2556_outVar));
              _2526_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2526_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2558_outName));
              RAST._IType _2559_outMaybeType;
              _2559_outMaybeType = (((_2557_outType).CanReadWithoutClone()) ? (_2557_outType) : (RAST.__default.MaybePlaceboType(_2557_outType)));
              _2527_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2527_paramTypes, _2558_outName, _2559_outMaybeType);
              RAST._IExpr _2560_outVarReturn;
              DCOMP._IOwnership _2561___v54;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2562___v55;
              RAST._IExpr _out101;
              DCOMP._IOwnership _out102;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
              (this).GenExpr(DAST.Expression.create_Ident((_2556_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2558_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_2558_outName, _2559_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
              _2560_outVarReturn = _out101;
              _2561___v54 = _out102;
              _2562___v55 = _out103;
              _2554_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2554_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2560_outVarReturn));
            }
            if ((new BigInteger((_2554_tupleArgs).Count)) == (BigInteger.One)) {
              _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_2554_tupleArgs).Select(BigInteger.Zero)));
            } else {
              _2551_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_2554_tupleArgs)));
            }
          }
        }
        _2549_env = DCOMP.Environment.create(_2526_paramNames, _2527_paramTypes);
        RAST._IExpr _2563_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2564___v56;
        DCOMP._IEnvironment _2565___v57;
        RAST._IExpr _out104;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
        DCOMP._IEnvironment _out106;
        (this).GenStmts((m).dtor_body, _2533_selfIdentifier, _2549_env, true, _2551_earlyReturn, out _out104, out _out105, out _out106);
        _2563_body = _out104;
        _2564___v56 = _out105;
        _2565___v57 = _out106;
        _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_2550_preBody).Then(_2563_body));
      } else {
        _2549_env = DCOMP.Environment.create(_2526_paramNames, _2527_paramTypes);
        _2548_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_2540_visibility, RAST.Fn.create(_2532_fnName, _2544_typeParams, _2525_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_2537_retTypeArgs).Count)) == (BigInteger.One)) ? ((_2537_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_2537_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2548_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2566_declarations;
      _2566_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2567_i;
      _2567_i = BigInteger.Zero;
      newEnv = env;
      while ((_2567_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2568_stmt;
        _2568_stmt = (stmts).Select(_2567_i);
        RAST._IExpr _2569_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2570_recIdents;
        DCOMP._IEnvironment _2571_newEnv2;
        RAST._IExpr _out107;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
        DCOMP._IEnvironment _out109;
        (this).GenStmt(_2568_stmt, selfIdent, newEnv, (isLast) && ((_2567_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out107, out _out108, out _out109);
        _2569_stmtExpr = _out107;
        _2570_recIdents = _out108;
        _2571_newEnv2 = _out109;
        newEnv = _2571_newEnv2;
        DAST._IStatement _source86 = _2568_stmt;
        if (_source86.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _2572___mcc_h0 = _source86.dtor_name;
          DAST._IType _2573___mcc_h1 = _source86.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _2574___mcc_h2 = _source86.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _2575_name = _2572___mcc_h0;
          {
            _2566_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2566_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_2575_name)));
          }
        } else if (_source86.is_Assign) {
          DAST._IAssignLhs _2576___mcc_h6 = _source86.dtor_lhs;
          DAST._IExpression _2577___mcc_h7 = _source86.dtor_value;
        } else if (_source86.is_If) {
          DAST._IExpression _2578___mcc_h10 = _source86.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2579___mcc_h11 = _source86.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _2580___mcc_h12 = _source86.dtor_els;
        } else if (_source86.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _2581___mcc_h16 = _source86.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _2582___mcc_h17 = _source86.dtor_body;
        } else if (_source86.is_While) {
          DAST._IExpression _2583___mcc_h20 = _source86.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2584___mcc_h21 = _source86.dtor_body;
        } else if (_source86.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _2585___mcc_h24 = _source86.dtor_boundName;
          DAST._IType _2586___mcc_h25 = _source86.dtor_boundType;
          DAST._IExpression _2587___mcc_h26 = _source86.dtor_over;
          Dafny.ISequence<DAST._IStatement> _2588___mcc_h27 = _source86.dtor_body;
        } else if (_source86.is_Call) {
          DAST._IExpression _2589___mcc_h32 = _source86.dtor_on;
          DAST._ICallName _2590___mcc_h33 = _source86.dtor_callName;
          Dafny.ISequence<DAST._IType> _2591___mcc_h34 = _source86.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2592___mcc_h35 = _source86.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2593___mcc_h36 = _source86.dtor_outs;
        } else if (_source86.is_Return) {
          DAST._IExpression _2594___mcc_h42 = _source86.dtor_expr;
        } else if (_source86.is_EarlyReturn) {
        } else if (_source86.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2595___mcc_h44 = _source86.dtor_toLabel;
        } else if (_source86.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _2596___mcc_h46 = _source86.dtor_body;
        } else if (_source86.is_JumpTailCallStart) {
        } else if (_source86.is_Halt) {
        } else {
          DAST._IExpression _2597___mcc_h48 = _source86.dtor_Print_i_a0;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2570_recIdents, _2566_declarations));
        generated = (generated).Then(_2569_stmtExpr);
        _2567_i = (_2567_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source87 = lhs;
      if (_source87.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2598___mcc_h0 = _source87.dtor_ident;
        Dafny.ISequence<Dafny.Rune> _source88 = _2598___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2599___mcc_h1 = _source88;
        Dafny.ISequence<Dafny.Rune> _2600_id = _2599___mcc_h1;
        {
          Dafny.ISequence<Dafny.Rune> _2601_idRust;
          _2601_idRust = DCOMP.__default.escapeName(_2600_id);
          if (((env).IsBorrowed(_2601_idRust)) || ((env).IsBorrowedMut(_2601_idRust))) {
            generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _2601_idRust), rhs);
          } else {
            generated = RAST.__default.AssignVar(_2601_idRust, rhs);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2601_idRust);
          needsIIFE = false;
        }
      } else if (_source87.is_Select) {
        DAST._IExpression _2602___mcc_h2 = _source87.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2603___mcc_h3 = _source87.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2604_field = _2603___mcc_h3;
        DAST._IExpression _2605_on = _2602___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _2606_fieldName;
          _2606_fieldName = DCOMP.__default.escapeName(_2604_field);
          RAST._IExpr _2607_onExpr;
          DCOMP._IOwnership _2608_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2609_recIdents;
          RAST._IExpr _out110;
          DCOMP._IOwnership _out111;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
          (this).GenExpr(_2605_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out110, out _out111, out _out112);
          _2607_onExpr = _out110;
          _2608_onOwned = _out111;
          _2609_recIdents = _out112;
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2607_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2606_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
          readIdents = _2609_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2610___mcc_h4 = _source87.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2611___mcc_h5 = _source87.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2612_indices = _2611___mcc_h5;
        DAST._IExpression _2613_on = _2610___mcc_h4;
        {
          RAST._IExpr _2614_onExpr;
          DCOMP._IOwnership _2615_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2616_recIdents;
          RAST._IExpr _out113;
          DCOMP._IOwnership _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          (this).GenExpr(_2613_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out113, out _out114, out _out115);
          _2614_onExpr = _out113;
          _2615_onOwned = _out114;
          _2616_recIdents = _out115;
          readIdents = _2616_recIdents;
          Dafny.ISequence<Dafny.Rune> _2617_r;
          _2617_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2618_i;
          _2618_i = BigInteger.Zero;
          while ((_2618_i) < (new BigInteger((_2612_indices).Count))) {
            RAST._IExpr _2619_idx;
            DCOMP._IOwnership _2620___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2621_recIdentsIdx;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr((_2612_indices).Select(_2618_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out116, out _out117, out _out118);
            _2619_idx = _out116;
            _2620___v61 = _out117;
            _2621_recIdentsIdx = _out118;
            _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2618_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2619_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2621_recIdentsIdx);
            _2618_i = (_2618_i) + (BigInteger.One);
          }
          _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, (_2614_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2618_i = BigInteger.Zero;
          while ((_2618_i) < (new BigInteger((_2612_indices).Count))) {
            _2617_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2618_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2618_i = (_2618_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2617_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source89 = stmt;
      if (_source89.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2622___mcc_h0 = _source89.dtor_name;
        DAST._IType _2623___mcc_h1 = _source89.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2624___mcc_h2 = _source89.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source90 = _2624___mcc_h2;
        if (_source90.is_None) {
          DAST._IType _2625_typ = _2623___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2626_name = _2622___mcc_h0;
          {
            DAST._IStatement _2627_newStmt;
            _2627_newStmt = DAST.Statement.create_DeclareVar(_2626_name, _2625_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_2625_typ)));
            RAST._IExpr _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            DCOMP._IEnvironment _out121;
            (this).GenStmt(_2627_newStmt, selfIdent, env, isLast, earlyReturn, out _out119, out _out120, out _out121);
            generated = _out119;
            readIdents = _out120;
            newEnv = _out121;
          }
        } else {
          DAST._IExpression _2628___mcc_h3 = _source90.dtor_value;
          DAST._IExpression _2629_expression = _2628___mcc_h3;
          DAST._IType _2630_typ = _2623___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2631_name = _2622___mcc_h0;
          {
            RAST._IType _2632_tpe;
            RAST._IType _out122;
            _out122 = (this).GenType(_2630_typ, true, false);
            _2632_tpe = _out122;
            Dafny.ISequence<Dafny.Rune> _2633_varName;
            _2633_varName = DCOMP.__default.escapeName(_2631_name);
            bool _2634_hasCopySemantics;
            _2634_hasCopySemantics = (_2632_tpe).CanReadWithoutClone();
            if (((_2629_expression).is_InitializationValue) && (!(_2634_hasCopySemantics))) {
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2633_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_2632_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              newEnv = (env).AddAssigned(_2633_varName, RAST.__default.MaybePlaceboType(_2632_tpe));
            } else {
              RAST._IExpr _2635_expr = RAST.Expr.Default();
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2636_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
              DCOMP._IOwnership _2637_exprOwnership = DCOMP.Ownership.Default();
              RAST._IExpr _out123;
              DCOMP._IOwnership _out124;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
              (this).GenExpr(_2629_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out123, out _out124, out _out125);
              _2635_expr = _out123;
              _2637_exprOwnership = _out124;
              _2636_recIdents = _out125;
              readIdents = _2636_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_2631_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2632_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2635_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_2631_name), _2632_tpe);
            }
          }
        }
      } else if (_source89.is_Assign) {
        DAST._IAssignLhs _2638___mcc_h4 = _source89.dtor_lhs;
        DAST._IExpression _2639___mcc_h5 = _source89.dtor_value;
        DAST._IExpression _2640_expression = _2639___mcc_h5;
        DAST._IAssignLhs _2641_lhs = _2638___mcc_h4;
        {
          RAST._IExpr _2642_exprGen;
          DCOMP._IOwnership _2643___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2644_exprIdents;
          RAST._IExpr _out126;
          DCOMP._IOwnership _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          (this).GenExpr(_2640_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
          _2642_exprGen = _out126;
          _2643___v62 = _out127;
          _2644_exprIdents = _out128;
          if ((_2641_lhs).is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2645_rustId;
            _2645_rustId = DCOMP.__default.escapeName(((_2641_lhs).dtor_ident));
            Std.Wrappers._IOption<RAST._IType> _2646_tpe;
            _2646_tpe = (env).GetType(_2645_rustId);
            if (((_2646_tpe).is_Some) && ((((_2646_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
              _2642_exprGen = RAST.__default.MaybePlacebo(_2642_exprGen);
            }
          }
          RAST._IExpr _2647_lhsGen;
          bool _2648_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2649_recIdents;
          DCOMP._IEnvironment _2650_resEnv;
          RAST._IExpr _out129;
          bool _out130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
          DCOMP._IEnvironment _out132;
          (this).GenAssignLhs(_2641_lhs, _2642_exprGen, selfIdent, env, out _out129, out _out130, out _out131, out _out132);
          _2647_lhsGen = _out129;
          _2648_needsIIFE = _out130;
          _2649_recIdents = _out131;
          _2650_resEnv = _out132;
          generated = _2647_lhsGen;
          newEnv = _2650_resEnv;
          if (_2648_needsIIFE) {
            generated = RAST.Expr.create_Block(generated);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2649_recIdents, _2644_exprIdents);
        }
      } else if (_source89.is_If) {
        DAST._IExpression _2651___mcc_h6 = _source89.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2652___mcc_h7 = _source89.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2653___mcc_h8 = _source89.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2654_elsDafny = _2653___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2655_thnDafny = _2652___mcc_h7;
        DAST._IExpression _2656_cond = _2651___mcc_h6;
        {
          RAST._IExpr _2657_cond;
          DCOMP._IOwnership _2658___v63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2659_recIdents;
          RAST._IExpr _out133;
          DCOMP._IOwnership _out134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
          (this).GenExpr(_2656_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
          _2657_cond = _out133;
          _2658___v63 = _out134;
          _2659_recIdents = _out135;
          Dafny.ISequence<Dafny.Rune> _2660_condString;
          _2660_condString = (_2657_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2659_recIdents;
          RAST._IExpr _2661_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2662_thnIdents;
          DCOMP._IEnvironment _2663_thnEnv;
          RAST._IExpr _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          DCOMP._IEnvironment _out138;
          (this).GenStmts(_2655_thnDafny, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
          _2661_thn = _out136;
          _2662_thnIdents = _out137;
          _2663_thnEnv = _out138;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2662_thnIdents);
          RAST._IExpr _2664_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2665_elsIdents;
          DCOMP._IEnvironment _2666_elsEnv;
          RAST._IExpr _out139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
          DCOMP._IEnvironment _out141;
          (this).GenStmts(_2654_elsDafny, selfIdent, env, isLast, earlyReturn, out _out139, out _out140, out _out141);
          _2664_els = _out139;
          _2665_elsIdents = _out140;
          _2666_elsEnv = _out141;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2665_elsIdents);
          newEnv = env;
          generated = RAST.Expr.create_IfExpr(_2657_cond, _2661_thn, _2664_els);
        }
      } else if (_source89.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2667___mcc_h9 = _source89.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2668___mcc_h10 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2669_body = _2668___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2670_lbl = _2667___mcc_h9;
        {
          RAST._IExpr _2671_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2672_bodyIdents;
          DCOMP._IEnvironment _2673_env2;
          RAST._IExpr _out142;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
          DCOMP._IEnvironment _out144;
          (this).GenStmts(_2669_body, selfIdent, env, isLast, earlyReturn, out _out142, out _out143, out _out144);
          _2671_body = _out142;
          _2672_bodyIdents = _out143;
          _2673_env2 = _out144;
          readIdents = _2672_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2670_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2671_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          newEnv = env;
        }
      } else if (_source89.is_While) {
        DAST._IExpression _2674___mcc_h11 = _source89.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2675___mcc_h12 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2676_body = _2675___mcc_h12;
        DAST._IExpression _2677_cond = _2674___mcc_h11;
        {
          RAST._IExpr _2678_cond;
          DCOMP._IOwnership _2679___v64;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2680_recIdents;
          RAST._IExpr _out145;
          DCOMP._IOwnership _out146;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
          (this).GenExpr(_2677_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
          _2678_cond = _out145;
          _2679___v64 = _out146;
          _2680_recIdents = _out147;
          readIdents = _2680_recIdents;
          RAST._IExpr _2681_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2682_bodyIdents;
          DCOMP._IEnvironment _2683_bodyEnv;
          RAST._IExpr _out148;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
          DCOMP._IEnvironment _out150;
          (this).GenStmts(_2676_body, selfIdent, env, false, earlyReturn, out _out148, out _out149, out _out150);
          _2681_bodyExpr = _out148;
          _2682_bodyIdents = _out149;
          _2683_bodyEnv = _out150;
          newEnv = env;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2682_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2678_cond), _2681_bodyExpr);
        }
      } else if (_source89.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2684___mcc_h13 = _source89.dtor_boundName;
        DAST._IType _2685___mcc_h14 = _source89.dtor_boundType;
        DAST._IExpression _2686___mcc_h15 = _source89.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2687___mcc_h16 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2688_body = _2687___mcc_h16;
        DAST._IExpression _2689_over = _2686___mcc_h15;
        DAST._IType _2690_boundType = _2685___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2691_boundName = _2684___mcc_h13;
        {
          RAST._IExpr _2692_over;
          DCOMP._IOwnership _2693___v65;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2694_recIdents;
          RAST._IExpr _out151;
          DCOMP._IOwnership _out152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
          (this).GenExpr(_2689_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out151, out _out152, out _out153);
          _2692_over = _out151;
          _2693___v65 = _out152;
          _2694_recIdents = _out153;
          RAST._IType _2695_boundTpe;
          RAST._IType _out154;
          _out154 = (this).GenType(_2690_boundType, false, false);
          _2695_boundTpe = _out154;
          readIdents = _2694_recIdents;
          Dafny.ISequence<Dafny.Rune> _2696_boundRName;
          _2696_boundRName = DCOMP.__default.escapeName(_2691_boundName);
          RAST._IExpr _2697_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2698_bodyIdents;
          DCOMP._IEnvironment _2699_bodyEnv;
          RAST._IExpr _out155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
          DCOMP._IEnvironment _out157;
          (this).GenStmts(_2688_body, selfIdent, (env).AddAssigned(_2696_boundRName, _2695_boundTpe), false, earlyReturn, out _out155, out _out156, out _out157);
          _2697_bodyExpr = _out155;
          _2698_bodyIdents = _out156;
          _2699_bodyEnv = _out157;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2698_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2696_boundRName));
          newEnv = env;
          generated = RAST.Expr.create_For(_2696_boundRName, _2692_over, _2697_bodyExpr);
        }
      } else if (_source89.is_Call) {
        DAST._IExpression _2700___mcc_h17 = _source89.dtor_on;
        DAST._ICallName _2701___mcc_h18 = _source89.dtor_callName;
        Dafny.ISequence<DAST._IType> _2702___mcc_h19 = _source89.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2703___mcc_h20 = _source89.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2704___mcc_h21 = _source89.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2705_maybeOutVars = _2704___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2706_args = _2703___mcc_h20;
        Dafny.ISequence<DAST._IType> _2707_typeArgs = _2702___mcc_h19;
        DAST._ICallName _2708_name = _2701___mcc_h18;
        DAST._IExpression _2709_on = _2700___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _2710_onExpr;
          DCOMP._IOwnership _2711___v68;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2712_enclosingIdents;
          RAST._IExpr _out158;
          DCOMP._IOwnership _out159;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
          (this).GenExpr(_2709_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out158, out _out159, out _out160);
          _2710_onExpr = _out158;
          _2711___v68 = _out159;
          _2712_enclosingIdents = _out160;
          Dafny.ISequence<RAST._IType> _2713_typeExprs;
          _2713_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_2707_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2714_typeI;
            _2714_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2715_typeArgsR;
            _2715_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2714_typeI) < (new BigInteger((_2707_typeArgs).Count))) {
              RAST._IType _2716_tpe;
              RAST._IType _out161;
              _out161 = (this).GenType((_2707_typeArgs).Select(_2714_typeI), false, false);
              _2716_tpe = _out161;
              _2715_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2715_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2716_tpe));
              _2714_typeI = (_2714_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _2717_argExprs;
          _2717_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi27 = new BigInteger((_2706_args).Count);
          for (BigInteger _2718_i = BigInteger.Zero; _2718_i < _hi27; _2718_i++) {
            DCOMP._IOwnership _2719_argOwnership;
            _2719_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_2708_name).is_CallName) && ((_2718_i) < (new BigInteger((((_2708_name).dtor_signature)).Count)))) {
              RAST._IType _2720_tpe;
              RAST._IType _out162;
              _out162 = (this).GenType(((((_2708_name).dtor_signature)).Select(_2718_i)).dtor_typ, false, false);
              _2720_tpe = _out162;
              if ((_2720_tpe).CanReadWithoutClone()) {
                _2719_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _2721_argExpr;
            DCOMP._IOwnership _2722_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2723_argIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr((_2706_args).Select(_2718_i), selfIdent, env, _2719_argOwnership, out _out163, out _out164, out _out165);
            _2721_argExpr = _out163;
            _2722_ownership = _out164;
            _2723_argIdents = _out165;
            _2717_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2717_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2721_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2723_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2712_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2724_renderedName;
          _2724_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source91) => {
            if (_source91.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _2725___mcc_h26 = _source91.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _2726___mcc_h27 = _source91.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _2727___mcc_h28 = _source91.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _2728_name = _2725___mcc_h26;
              return DCOMP.__default.escapeName(_2728_name);
            } else if (_source91.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source91.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source91.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2708_name);
          DAST._IExpression _source92 = _2709_on;
          if (_source92.is_Literal) {
            DAST._ILiteral _2729___mcc_h29 = _source92.dtor_Literal_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2730___mcc_h31 = _source92.dtor_Ident_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2731___mcc_h33 = _source92.dtor_Companion_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).MSel(_2724_renderedName);
            }
          } else if (_source92.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2732___mcc_h35 = _source92.dtor_Tuple_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2733___mcc_h37 = _source92.dtor_path;
            Dafny.ISequence<DAST._IType> _2734___mcc_h38 = _source92.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2735___mcc_h39 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2736___mcc_h43 = _source92.dtor_dims;
            DAST._IType _2737___mcc_h44 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_DatatypeValue) {
            DAST._IDatatypeType _2738___mcc_h47 = _source92.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _2739___mcc_h48 = _source92.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2740___mcc_h49 = _source92.dtor_variant;
            bool _2741___mcc_h50 = _source92.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2742___mcc_h51 = _source92.dtor_contents;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Convert) {
            DAST._IExpression _2743___mcc_h57 = _source92.dtor_value;
            DAST._IType _2744___mcc_h58 = _source92.dtor_from;
            DAST._IType _2745___mcc_h59 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqConstruct) {
            DAST._IExpression _2746___mcc_h63 = _source92.dtor_length;
            DAST._IExpression _2747___mcc_h64 = _source92.dtor_elem;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2748___mcc_h67 = _source92.dtor_elements;
            DAST._IType _2749___mcc_h68 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2750___mcc_h71 = _source92.dtor_elements;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2751___mcc_h73 = _source92.dtor_elements;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2752___mcc_h75 = _source92.dtor_mapElems;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapBuilder) {
            DAST._IType _2753___mcc_h77 = _source92.dtor_keyType;
            DAST._IType _2754___mcc_h78 = _source92.dtor_valueType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqUpdate) {
            DAST._IExpression _2755___mcc_h81 = _source92.dtor_expr;
            DAST._IExpression _2756___mcc_h82 = _source92.dtor_indexExpr;
            DAST._IExpression _2757___mcc_h83 = _source92.dtor_value;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapUpdate) {
            DAST._IExpression _2758___mcc_h87 = _source92.dtor_expr;
            DAST._IExpression _2759___mcc_h88 = _source92.dtor_indexExpr;
            DAST._IExpression _2760___mcc_h89 = _source92.dtor_value;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetBuilder) {
            DAST._IType _2761___mcc_h93 = _source92.dtor_elemType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_ToMultiset) {
            DAST._IExpression _2762___mcc_h95 = _source92.dtor_ToMultiset_i_a0;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_This) {
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Ite) {
            DAST._IExpression _2763___mcc_h97 = _source92.dtor_cond;
            DAST._IExpression _2764___mcc_h98 = _source92.dtor_thn;
            DAST._IExpression _2765___mcc_h99 = _source92.dtor_els;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_UnOp) {
            DAST._IUnaryOp _2766___mcc_h103 = _source92.dtor_unOp;
            DAST._IExpression _2767___mcc_h104 = _source92.dtor_expr;
            DAST.Format._IUnaryOpFormat _2768___mcc_h105 = _source92.dtor_format1;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BinOp) {
            DAST._IBinOp _2769___mcc_h109 = _source92.dtor_op;
            DAST._IExpression _2770___mcc_h110 = _source92.dtor_left;
            DAST._IExpression _2771___mcc_h111 = _source92.dtor_right;
            DAST.Format._IBinaryOpFormat _2772___mcc_h112 = _source92.dtor_format2;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_ArrayLen) {
            DAST._IExpression _2773___mcc_h117 = _source92.dtor_expr;
            BigInteger _2774___mcc_h118 = _source92.dtor_dim;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapKeys) {
            DAST._IExpression _2775___mcc_h121 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_MapValues) {
            DAST._IExpression _2776___mcc_h123 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Select) {
            DAST._IExpression _2777___mcc_h125 = _source92.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2778___mcc_h126 = _source92.dtor_field;
            bool _2779___mcc_h127 = _source92.dtor_isConstant;
            bool _2780___mcc_h128 = _source92.dtor_onDatatype;
            DAST._IType _2781___mcc_h129 = _source92.dtor_fieldType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SelectFn) {
            DAST._IExpression _2782___mcc_h135 = _source92.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2783___mcc_h136 = _source92.dtor_field;
            bool _2784___mcc_h137 = _source92.dtor_onDatatype;
            bool _2785___mcc_h138 = _source92.dtor_isStatic;
            BigInteger _2786___mcc_h139 = _source92.dtor_arity;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Index) {
            DAST._IExpression _2787___mcc_h145 = _source92.dtor_expr;
            DAST._ICollKind _2788___mcc_h146 = _source92.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2789___mcc_h147 = _source92.dtor_indices;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_IndexRange) {
            DAST._IExpression _2790___mcc_h151 = _source92.dtor_expr;
            bool _2791___mcc_h152 = _source92.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2792___mcc_h153 = _source92.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2793___mcc_h154 = _source92.dtor_high;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_TupleSelect) {
            DAST._IExpression _2794___mcc_h159 = _source92.dtor_expr;
            BigInteger _2795___mcc_h160 = _source92.dtor_index;
            DAST._IType _2796___mcc_h161 = _source92.dtor_fieldType;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Call) {
            DAST._IExpression _2797___mcc_h165 = _source92.dtor_on;
            DAST._ICallName _2798___mcc_h166 = _source92.dtor_callName;
            Dafny.ISequence<DAST._IType> _2799___mcc_h167 = _source92.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2800___mcc_h168 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2801___mcc_h173 = _source92.dtor_params;
            DAST._IType _2802___mcc_h174 = _source92.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2803___mcc_h175 = _source92.dtor_body;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2804___mcc_h179 = _source92.dtor_values;
            DAST._IType _2805___mcc_h180 = _source92.dtor_retType;
            DAST._IExpression _2806___mcc_h181 = _source92.dtor_expr;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2807___mcc_h185 = _source92.dtor_name;
            DAST._IType _2808___mcc_h186 = _source92.dtor_typ;
            DAST._IExpression _2809___mcc_h187 = _source92.dtor_value;
            DAST._IExpression _2810___mcc_h188 = _source92.dtor_iifeBody;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_Apply) {
            DAST._IExpression _2811___mcc_h193 = _source92.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2812___mcc_h194 = _source92.dtor_args;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_TypeTest) {
            DAST._IExpression _2813___mcc_h197 = _source92.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2814___mcc_h198 = _source92.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2815___mcc_h199 = _source92.dtor_variant;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_InitializationValue) {
            DAST._IType _2816___mcc_h203 = _source92.dtor_typ;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_BoolBoundedPool) {
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SetBoundedPool) {
            DAST._IExpression _2817___mcc_h205 = _source92.dtor_of;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_SeqBoundedPool) {
            DAST._IExpression _2818___mcc_h207 = _source92.dtor_of;
            bool _2819___mcc_h208 = _source92.dtor_includeDuplicates;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else if (_source92.is_IntRange) {
            DAST._IExpression _2820___mcc_h211 = _source92.dtor_lo;
            DAST._IExpression _2821___mcc_h212 = _source92.dtor_hi;
            bool _2822___mcc_h213 = _source92.dtor_up;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          } else {
            DAST._IExpression _2823___mcc_h217 = _source92.dtor_start;
            bool _2824___mcc_h218 = _source92.dtor_up;
            {
              _2710_onExpr = (_2710_onExpr).Sel(_2724_renderedName);
            }
          }
          generated = _2710_onExpr;
          if ((new BigInteger((_2713_typeExprs).Count)).Sign == 1) {
            generated = (generated).ApplyType(_2713_typeExprs);
          }
          generated = (generated).Apply(_2717_argExprs);
          if (((_2705_maybeOutVars).is_Some) && ((new BigInteger(((_2705_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
            Dafny.ISequence<Dafny.Rune> _2825_outVar;
            _2825_outVar = DCOMP.__default.escapeName((((_2705_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
            if (!((env).CanReadWithoutClone(_2825_outVar))) {
              generated = RAST.__default.MaybePlacebo(generated);
            }
            generated = RAST.__default.AssignVar(_2825_outVar, generated);
          } else if (((_2705_maybeOutVars).is_None) || ((new BigInteger(((_2705_maybeOutVars).dtor_value).Count)).Sign == 0)) {
          } else {
            Dafny.ISequence<Dafny.Rune> _2826_tmpVar;
            _2826_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
            RAST._IExpr _2827_tmpId;
            _2827_tmpId = RAST.Expr.create_Identifier(_2826_tmpVar);
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2826_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2828_outVars;
            _2828_outVars = (_2705_maybeOutVars).dtor_value;
            BigInteger _hi28 = new BigInteger((_2828_outVars).Count);
            for (BigInteger _2829_outI = BigInteger.Zero; _2829_outI < _hi28; _2829_outI++) {
              Dafny.ISequence<Dafny.Rune> _2830_outVar;
              _2830_outVar = DCOMP.__default.escapeName(((_2828_outVars).Select(_2829_outI)));
              RAST._IExpr _2831_rhs;
              _2831_rhs = (_2827_tmpId).Sel(Std.Strings.__default.OfNat(_2829_outI));
              if (!((env).CanReadWithoutClone(_2830_outVar))) {
                _2831_rhs = RAST.__default.MaybePlacebo(_2831_rhs);
              }
              generated = (generated).Then(RAST.__default.AssignVar(_2830_outVar, _2831_rhs));
            }
          }
          newEnv = env;
        }
      } else if (_source89.is_Return) {
        DAST._IExpression _2832___mcc_h22 = _source89.dtor_expr;
        DAST._IExpression _2833_exprDafny = _2832___mcc_h22;
        {
          RAST._IExpr _2834_expr;
          DCOMP._IOwnership _2835___v73;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2836_recIdents;
          RAST._IExpr _out166;
          DCOMP._IOwnership _out167;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
          (this).GenExpr(_2833_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
          _2834_expr = _out166;
          _2835___v73 = _out167;
          _2836_recIdents = _out168;
          readIdents = _2836_recIdents;
          if (isLast) {
            generated = _2834_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2834_expr));
          }
          newEnv = env;
        }
      } else if (_source89.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2837___mcc_h23 = _source89.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2838_toLabel = _2837___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source93 = _2838_toLabel;
          if (_source93.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2839___mcc_h221 = _source93.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2840_lbl = _2839___mcc_h221;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2840_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2841___mcc_h24 = _source89.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2842_body = _2841___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
          }
          newEnv = env;
          BigInteger _hi29 = new BigInteger(((env).dtor_names).Count);
          for (BigInteger _2843_paramI = BigInteger.Zero; _2843_paramI < _hi29; _2843_paramI++) {
            Dafny.ISequence<Dafny.Rune> _2844_param;
            _2844_param = ((env).dtor_names).Select(_2843_paramI);
            RAST._IExpr _2845_paramInit;
            DCOMP._IOwnership _2846___v66;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2847___v67;
            RAST._IExpr _out169;
            DCOMP._IOwnership _out170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
            (this).GenIdent(_2844_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out169, out _out170, out _out171);
            _2845_paramInit = _out169;
            _2846___v66 = _out170;
            _2847___v67 = _out171;
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2844_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2845_paramInit)));
            if (((env).dtor_types).Contains(_2844_param)) {
              RAST._IType _2848_declaredType;
              _2848_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_2844_param)).ToOwned();
              newEnv = (newEnv).AddAssigned(_2844_param, _2848_declaredType);
            }
          }
          RAST._IExpr _2849_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2850_bodyIdents;
          DCOMP._IEnvironment _2851_bodyEnv;
          RAST._IExpr _out172;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
          DCOMP._IEnvironment _out174;
          (this).GenStmts(_2842_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out172, out _out173, out _out174);
          _2849_bodyExpr = _out172;
          _2850_bodyIdents = _out173;
          _2851_bodyEnv = _out174;
          readIdents = _2850_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2849_bodyExpr)));
        }
      } else if (_source89.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source89.is_Halt) {
        {
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else {
        DAST._IExpression _2852___mcc_h25 = _source89.dtor_Print_i_a0;
        DAST._IExpression _2853_e = _2852___mcc_h25;
        {
          RAST._IExpr _2854_printedExpr;
          DCOMP._IOwnership _2855_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2856_recIdents;
          RAST._IExpr _out175;
          DCOMP._IOwnership _out176;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
          (this).GenExpr(_2853_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out175, out _out176, out _out177);
          _2854_printedExpr = _out175;
          _2855_recOwnership = _out176;
          _2856_recIdents = _out177;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_2854_printedExpr)));
          readIdents = _2856_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source94 = range;
      if (_source94.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source94.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source94.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source94.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source94.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source94.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source94.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source94.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source94.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source94.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source94.is_BigInt) {
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
        RAST._IExpr _out178;
        DCOMP._IOwnership _out179;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
        @out = _out178;
        resultingOwnership = _out179;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out180;
        DCOMP._IOwnership _out181;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out180, out _out181);
        @out = _out180;
        resultingOwnership = _out181;
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
      DAST._IExpression _source95 = e;
      DAST._ILiteral _2857___mcc_h0 = _source95.dtor_Literal_i_a0;
      DAST._ILiteral _source96 = _2857___mcc_h0;
      if (_source96.is_BoolLiteral) {
        bool _2858___mcc_h1 = _source96.dtor_BoolLiteral_i_a0;
        bool _2859_b = _2858___mcc_h1;
        {
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_2859_b), expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2860___mcc_h2 = _source96.dtor_IntLiteral_i_a0;
        DAST._IType _2861___mcc_h3 = _source96.dtor_IntLiteral_i_a1;
        DAST._IType _2862_t = _2861___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2863_i = _2860___mcc_h2;
        {
          DAST._IType _source97 = _2862_t;
          if (_source97.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2864___mcc_h105 = _source97.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2865___mcc_h106 = _source97.dtor_typeArgs;
            DAST._IResolvedType _2866___mcc_h107 = _source97.dtor_resolved;
            DAST._IType _2867_o = _2862_t;
            {
              RAST._IType _2868_genType;
              RAST._IType _out184;
              _out184 = (this).GenType(_2867_o, false, false);
              _2868_genType = _out184;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2868_genType);
            }
          } else if (_source97.is_Nullable) {
            DAST._IType _2869___mcc_h111 = _source97.dtor_Nullable_i_a0;
            DAST._IType _2870_o = _2862_t;
            {
              RAST._IType _2871_genType;
              RAST._IType _out185;
              _out185 = (this).GenType(_2870_o, false, false);
              _2871_genType = _out185;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2871_genType);
            }
          } else if (_source97.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2872___mcc_h113 = _source97.dtor_Tuple_i_a0;
            DAST._IType _2873_o = _2862_t;
            {
              RAST._IType _2874_genType;
              RAST._IType _out186;
              _out186 = (this).GenType(_2873_o, false, false);
              _2874_genType = _out186;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2874_genType);
            }
          } else if (_source97.is_Array) {
            DAST._IType _2875___mcc_h115 = _source97.dtor_element;
            BigInteger _2876___mcc_h116 = _source97.dtor_dims;
            DAST._IType _2877_o = _2862_t;
            {
              RAST._IType _2878_genType;
              RAST._IType _out187;
              _out187 = (this).GenType(_2877_o, false, false);
              _2878_genType = _out187;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2878_genType);
            }
          } else if (_source97.is_Seq) {
            DAST._IType _2879___mcc_h119 = _source97.dtor_element;
            DAST._IType _2880_o = _2862_t;
            {
              RAST._IType _2881_genType;
              RAST._IType _out188;
              _out188 = (this).GenType(_2880_o, false, false);
              _2881_genType = _out188;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2881_genType);
            }
          } else if (_source97.is_Set) {
            DAST._IType _2882___mcc_h121 = _source97.dtor_element;
            DAST._IType _2883_o = _2862_t;
            {
              RAST._IType _2884_genType;
              RAST._IType _out189;
              _out189 = (this).GenType(_2883_o, false, false);
              _2884_genType = _out189;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2884_genType);
            }
          } else if (_source97.is_Multiset) {
            DAST._IType _2885___mcc_h123 = _source97.dtor_element;
            DAST._IType _2886_o = _2862_t;
            {
              RAST._IType _2887_genType;
              RAST._IType _out190;
              _out190 = (this).GenType(_2886_o, false, false);
              _2887_genType = _out190;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2887_genType);
            }
          } else if (_source97.is_Map) {
            DAST._IType _2888___mcc_h125 = _source97.dtor_key;
            DAST._IType _2889___mcc_h126 = _source97.dtor_value;
            DAST._IType _2890_o = _2862_t;
            {
              RAST._IType _2891_genType;
              RAST._IType _out191;
              _out191 = (this).GenType(_2890_o, false, false);
              _2891_genType = _out191;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2891_genType);
            }
          } else if (_source97.is_SetBuilder) {
            DAST._IType _2892___mcc_h129 = _source97.dtor_element;
            DAST._IType _2893_o = _2862_t;
            {
              RAST._IType _2894_genType;
              RAST._IType _out192;
              _out192 = (this).GenType(_2893_o, false, false);
              _2894_genType = _out192;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2894_genType);
            }
          } else if (_source97.is_MapBuilder) {
            DAST._IType _2895___mcc_h131 = _source97.dtor_key;
            DAST._IType _2896___mcc_h132 = _source97.dtor_value;
            DAST._IType _2897_o = _2862_t;
            {
              RAST._IType _2898_genType;
              RAST._IType _out193;
              _out193 = (this).GenType(_2897_o, false, false);
              _2898_genType = _out193;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2898_genType);
            }
          } else if (_source97.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2899___mcc_h135 = _source97.dtor_args;
            DAST._IType _2900___mcc_h136 = _source97.dtor_result;
            DAST._IType _2901_o = _2862_t;
            {
              RAST._IType _2902_genType;
              RAST._IType _out194;
              _out194 = (this).GenType(_2901_o, false, false);
              _2902_genType = _out194;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2902_genType);
            }
          } else if (_source97.is_Primitive) {
            DAST._IPrimitive _2903___mcc_h139 = _source97.dtor_Primitive_i_a0;
            DAST._IPrimitive _source98 = _2903___mcc_h139;
            if (_source98.is_Int) {
              {
                if ((new BigInteger((_2863_i).Count)) <= (new BigInteger(4))) {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_2863_i));
                } else {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_2863_i, true));
                }
              }
            } else if (_source98.is_Real) {
              DAST._IType _2904_o = _2862_t;
              {
                RAST._IType _2905_genType;
                RAST._IType _out195;
                _out195 = (this).GenType(_2904_o, false, false);
                _2905_genType = _out195;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2905_genType);
              }
            } else if (_source98.is_String) {
              DAST._IType _2906_o = _2862_t;
              {
                RAST._IType _2907_genType;
                RAST._IType _out196;
                _out196 = (this).GenType(_2906_o, false, false);
                _2907_genType = _out196;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2907_genType);
              }
            } else if (_source98.is_Bool) {
              DAST._IType _2908_o = _2862_t;
              {
                RAST._IType _2909_genType;
                RAST._IType _out197;
                _out197 = (this).GenType(_2908_o, false, false);
                _2909_genType = _out197;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2909_genType);
              }
            } else {
              DAST._IType _2910_o = _2862_t;
              {
                RAST._IType _2911_genType;
                RAST._IType _out198;
                _out198 = (this).GenType(_2910_o, false, false);
                _2911_genType = _out198;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2911_genType);
              }
            }
          } else if (_source97.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2912___mcc_h141 = _source97.dtor_Passthrough_i_a0;
            DAST._IType _2913_o = _2862_t;
            {
              RAST._IType _2914_genType;
              RAST._IType _out199;
              _out199 = (this).GenType(_2913_o, false, false);
              _2914_genType = _out199;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2914_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2915___mcc_h143 = _source97.dtor_TypeArg_i_a0;
            DAST._IType _2916_o = _2862_t;
            {
              RAST._IType _2917_genType;
              RAST._IType _out200;
              _out200 = (this).GenType(_2916_o, false, false);
              _2917_genType = _out200;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2863_i), _2917_genType);
            }
          }
          RAST._IExpr _out201;
          DCOMP._IOwnership _out202;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out201, out _out202);
          r = _out201;
          resultingOwnership = _out202;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2918___mcc_h4 = _source96.dtor_DecLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2919___mcc_h5 = _source96.dtor_DecLiteral_i_a1;
        DAST._IType _2920___mcc_h6 = _source96.dtor_DecLiteral_i_a2;
        DAST._IType _2921_t = _2920___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2922_d = _2919___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2923_n = _2918___mcc_h4;
        {
          DAST._IType _source99 = _2921_t;
          if (_source99.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2924___mcc_h145 = _source99.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2925___mcc_h146 = _source99.dtor_typeArgs;
            DAST._IResolvedType _2926___mcc_h147 = _source99.dtor_resolved;
            DAST._IType _2927_o = _2921_t;
            {
              RAST._IType _2928_genType;
              RAST._IType _out203;
              _out203 = (this).GenType(_2927_o, false, false);
              _2928_genType = _out203;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2928_genType);
            }
          } else if (_source99.is_Nullable) {
            DAST._IType _2929___mcc_h151 = _source99.dtor_Nullable_i_a0;
            DAST._IType _2930_o = _2921_t;
            {
              RAST._IType _2931_genType;
              RAST._IType _out204;
              _out204 = (this).GenType(_2930_o, false, false);
              _2931_genType = _out204;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2931_genType);
            }
          } else if (_source99.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2932___mcc_h153 = _source99.dtor_Tuple_i_a0;
            DAST._IType _2933_o = _2921_t;
            {
              RAST._IType _2934_genType;
              RAST._IType _out205;
              _out205 = (this).GenType(_2933_o, false, false);
              _2934_genType = _out205;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2934_genType);
            }
          } else if (_source99.is_Array) {
            DAST._IType _2935___mcc_h155 = _source99.dtor_element;
            BigInteger _2936___mcc_h156 = _source99.dtor_dims;
            DAST._IType _2937_o = _2921_t;
            {
              RAST._IType _2938_genType;
              RAST._IType _out206;
              _out206 = (this).GenType(_2937_o, false, false);
              _2938_genType = _out206;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2938_genType);
            }
          } else if (_source99.is_Seq) {
            DAST._IType _2939___mcc_h159 = _source99.dtor_element;
            DAST._IType _2940_o = _2921_t;
            {
              RAST._IType _2941_genType;
              RAST._IType _out207;
              _out207 = (this).GenType(_2940_o, false, false);
              _2941_genType = _out207;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2941_genType);
            }
          } else if (_source99.is_Set) {
            DAST._IType _2942___mcc_h161 = _source99.dtor_element;
            DAST._IType _2943_o = _2921_t;
            {
              RAST._IType _2944_genType;
              RAST._IType _out208;
              _out208 = (this).GenType(_2943_o, false, false);
              _2944_genType = _out208;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2944_genType);
            }
          } else if (_source99.is_Multiset) {
            DAST._IType _2945___mcc_h163 = _source99.dtor_element;
            DAST._IType _2946_o = _2921_t;
            {
              RAST._IType _2947_genType;
              RAST._IType _out209;
              _out209 = (this).GenType(_2946_o, false, false);
              _2947_genType = _out209;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2947_genType);
            }
          } else if (_source99.is_Map) {
            DAST._IType _2948___mcc_h165 = _source99.dtor_key;
            DAST._IType _2949___mcc_h166 = _source99.dtor_value;
            DAST._IType _2950_o = _2921_t;
            {
              RAST._IType _2951_genType;
              RAST._IType _out210;
              _out210 = (this).GenType(_2950_o, false, false);
              _2951_genType = _out210;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2951_genType);
            }
          } else if (_source99.is_SetBuilder) {
            DAST._IType _2952___mcc_h169 = _source99.dtor_element;
            DAST._IType _2953_o = _2921_t;
            {
              RAST._IType _2954_genType;
              RAST._IType _out211;
              _out211 = (this).GenType(_2953_o, false, false);
              _2954_genType = _out211;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2954_genType);
            }
          } else if (_source99.is_MapBuilder) {
            DAST._IType _2955___mcc_h171 = _source99.dtor_key;
            DAST._IType _2956___mcc_h172 = _source99.dtor_value;
            DAST._IType _2957_o = _2921_t;
            {
              RAST._IType _2958_genType;
              RAST._IType _out212;
              _out212 = (this).GenType(_2957_o, false, false);
              _2958_genType = _out212;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2958_genType);
            }
          } else if (_source99.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2959___mcc_h175 = _source99.dtor_args;
            DAST._IType _2960___mcc_h176 = _source99.dtor_result;
            DAST._IType _2961_o = _2921_t;
            {
              RAST._IType _2962_genType;
              RAST._IType _out213;
              _out213 = (this).GenType(_2961_o, false, false);
              _2962_genType = _out213;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2962_genType);
            }
          } else if (_source99.is_Primitive) {
            DAST._IPrimitive _2963___mcc_h179 = _source99.dtor_Primitive_i_a0;
            DAST._IPrimitive _source100 = _2963___mcc_h179;
            if (_source100.is_Int) {
              DAST._IType _2964_o = _2921_t;
              {
                RAST._IType _2965_genType;
                RAST._IType _out214;
                _out214 = (this).GenType(_2964_o, false, false);
                _2965_genType = _out214;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2965_genType);
              }
            } else if (_source100.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source100.is_String) {
              DAST._IType _2966_o = _2921_t;
              {
                RAST._IType _2967_genType;
                RAST._IType _out215;
                _out215 = (this).GenType(_2966_o, false, false);
                _2967_genType = _out215;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2967_genType);
              }
            } else if (_source100.is_Bool) {
              DAST._IType _2968_o = _2921_t;
              {
                RAST._IType _2969_genType;
                RAST._IType _out216;
                _out216 = (this).GenType(_2968_o, false, false);
                _2969_genType = _out216;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2969_genType);
              }
            } else {
              DAST._IType _2970_o = _2921_t;
              {
                RAST._IType _2971_genType;
                RAST._IType _out217;
                _out217 = (this).GenType(_2970_o, false, false);
                _2971_genType = _out217;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2971_genType);
              }
            }
          } else if (_source99.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2972___mcc_h181 = _source99.dtor_Passthrough_i_a0;
            DAST._IType _2973_o = _2921_t;
            {
              RAST._IType _2974_genType;
              RAST._IType _out218;
              _out218 = (this).GenType(_2973_o, false, false);
              _2974_genType = _out218;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2974_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2975___mcc_h183 = _source99.dtor_TypeArg_i_a0;
            DAST._IType _2976_o = _2921_t;
            {
              RAST._IType _2977_genType;
              RAST._IType _out219;
              _out219 = (this).GenType(_2976_o, false, false);
              _2977_genType = _out219;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2923_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2922_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2977_genType);
            }
          }
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2978___mcc_h7 = _source96.dtor_StringLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2979_l = _2978___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_2979_l, false));
          RAST._IExpr _out222;
          DCOMP._IOwnership _out223;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out222, out _out223);
          r = _out222;
          resultingOwnership = _out223;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source96.is_CharLiteral) {
        Dafny.Rune _2980___mcc_h8 = _source96.dtor_CharLiteral_i_a0;
        Dafny.Rune _2981_c = _2980___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2981_c).Value)));
          if (!((this).UnicodeChars)) {
            r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
          } else {
            r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          }
          r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
          RAST._IExpr _out224;
          DCOMP._IOwnership _out225;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out224, out _out225);
          r = _out224;
          resultingOwnership = _out225;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else {
        DAST._IType _2982___mcc_h9 = _source96.dtor_Null_i_a0;
        DAST._IType _2983_tpe = _2982___mcc_h9;
        {
          RAST._IType _2984_tpeGen;
          RAST._IType _out226;
          _out226 = (this).GenType(_2983_tpe, false, false);
          _2984_tpeGen = _out226;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2984_tpeGen);
          RAST._IExpr _out227;
          DCOMP._IOwnership _out228;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out227, out _out228);
          r = _out227;
          resultingOwnership = _out228;
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
      DAST._IBinOp _2985_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _2986_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _2987_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _2988_format = _let_tmp_rhs52.dtor_format2;
      bool _2989_becomesLeftCallsRight;
      _2989_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source101) => {
        if (_source101.is_Eq) {
          bool _2990___mcc_h0 = _source101.dtor_referential;
          bool _2991___mcc_h1 = _source101.dtor_nullable;
          return false;
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
          Dafny.ISequence<Dafny.Rune> _2992___mcc_h4 = _source101.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2985_op);
      bool _2993_becomesRightCallsLeft;
      _2993_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source102) => {
        if (_source102.is_Eq) {
          bool _2994___mcc_h6 = _source102.dtor_referential;
          bool _2995___mcc_h7 = _source102.dtor_nullable;
          return false;
        } else if (_source102.is_Div) {
          return false;
        } else if (_source102.is_EuclidianDiv) {
          return false;
        } else if (_source102.is_Mod) {
          return false;
        } else if (_source102.is_EuclidianMod) {
          return false;
        } else if (_source102.is_Lt) {
          return false;
        } else if (_source102.is_LtChar) {
          return false;
        } else if (_source102.is_Plus) {
          return false;
        } else if (_source102.is_Minus) {
          return false;
        } else if (_source102.is_Times) {
          return false;
        } else if (_source102.is_BitwiseAnd) {
          return false;
        } else if (_source102.is_BitwiseOr) {
          return false;
        } else if (_source102.is_BitwiseXor) {
          return false;
        } else if (_source102.is_BitwiseShiftRight) {
          return false;
        } else if (_source102.is_BitwiseShiftLeft) {
          return false;
        } else if (_source102.is_And) {
          return false;
        } else if (_source102.is_Or) {
          return false;
        } else if (_source102.is_In) {
          return true;
        } else if (_source102.is_SeqProperPrefix) {
          return false;
        } else if (_source102.is_SeqPrefix) {
          return false;
        } else if (_source102.is_SetMerge) {
          return false;
        } else if (_source102.is_SetSubtraction) {
          return false;
        } else if (_source102.is_SetIntersection) {
          return false;
        } else if (_source102.is_Subset) {
          return false;
        } else if (_source102.is_ProperSubset) {
          return false;
        } else if (_source102.is_SetDisjoint) {
          return false;
        } else if (_source102.is_MapMerge) {
          return false;
        } else if (_source102.is_MapSubtraction) {
          return false;
        } else if (_source102.is_MultisetMerge) {
          return false;
        } else if (_source102.is_MultisetSubtraction) {
          return false;
        } else if (_source102.is_MultisetIntersection) {
          return false;
        } else if (_source102.is_Submultiset) {
          return false;
        } else if (_source102.is_ProperSubmultiset) {
          return false;
        } else if (_source102.is_MultisetDisjoint) {
          return false;
        } else if (_source102.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2996___mcc_h10 = _source102.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2985_op);
      bool _2997_becomesCallLeftRight;
      _2997_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source103) => {
        if (_source103.is_Eq) {
          bool _2998___mcc_h12 = _source103.dtor_referential;
          bool _2999___mcc_h13 = _source103.dtor_nullable;
          if ((_2998___mcc_h12) == (true)) {
            if ((_2999___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source103.is_Div) {
          return false;
        } else if (_source103.is_EuclidianDiv) {
          return false;
        } else if (_source103.is_Mod) {
          return false;
        } else if (_source103.is_EuclidianMod) {
          return false;
        } else if (_source103.is_Lt) {
          return false;
        } else if (_source103.is_LtChar) {
          return false;
        } else if (_source103.is_Plus) {
          return false;
        } else if (_source103.is_Minus) {
          return false;
        } else if (_source103.is_Times) {
          return false;
        } else if (_source103.is_BitwiseAnd) {
          return false;
        } else if (_source103.is_BitwiseOr) {
          return false;
        } else if (_source103.is_BitwiseXor) {
          return false;
        } else if (_source103.is_BitwiseShiftRight) {
          return false;
        } else if (_source103.is_BitwiseShiftLeft) {
          return false;
        } else if (_source103.is_And) {
          return false;
        } else if (_source103.is_Or) {
          return false;
        } else if (_source103.is_In) {
          return false;
        } else if (_source103.is_SeqProperPrefix) {
          return false;
        } else if (_source103.is_SeqPrefix) {
          return false;
        } else if (_source103.is_SetMerge) {
          return true;
        } else if (_source103.is_SetSubtraction) {
          return true;
        } else if (_source103.is_SetIntersection) {
          return true;
        } else if (_source103.is_Subset) {
          return false;
        } else if (_source103.is_ProperSubset) {
          return false;
        } else if (_source103.is_SetDisjoint) {
          return true;
        } else if (_source103.is_MapMerge) {
          return true;
        } else if (_source103.is_MapSubtraction) {
          return true;
        } else if (_source103.is_MultisetMerge) {
          return true;
        } else if (_source103.is_MultisetSubtraction) {
          return true;
        } else if (_source103.is_MultisetIntersection) {
          return true;
        } else if (_source103.is_Submultiset) {
          return false;
        } else if (_source103.is_ProperSubmultiset) {
          return false;
        } else if (_source103.is_MultisetDisjoint) {
          return true;
        } else if (_source103.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _3000___mcc_h16 = _source103.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2985_op);
      DCOMP._IOwnership _3001_expectedLeftOwnership;
      _3001_expectedLeftOwnership = ((_2989_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2993_becomesRightCallsLeft) || (_2997_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _3002_expectedRightOwnership;
      _3002_expectedRightOwnership = (((_2989_becomesLeftCallsRight) || (_2997_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2993_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _3003_left;
      DCOMP._IOwnership _3004___v78;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3005_recIdentsL;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_2986_lExpr, selfIdent, env, _3001_expectedLeftOwnership, out _out229, out _out230, out _out231);
      _3003_left = _out229;
      _3004___v78 = _out230;
      _3005_recIdentsL = _out231;
      RAST._IExpr _3006_right;
      DCOMP._IOwnership _3007___v79;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3008_recIdentsR;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
      (this).GenExpr(_2987_rExpr, selfIdent, env, _3002_expectedRightOwnership, out _out232, out _out233, out _out234);
      _3006_right = _out232;
      _3007___v79 = _out233;
      _3008_recIdentsR = _out234;
      DAST._IBinOp _source104 = _2985_op;
      if (_source104.is_Eq) {
        bool _3009___mcc_h18 = _source104.dtor_referential;
        bool _3010___mcc_h19 = _source104.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source105 = _2985_op;
            if (_source105.is_Eq) {
              bool _3011___mcc_h24 = _source105.dtor_referential;
              bool _3012___mcc_h25 = _source105.dtor_nullable;
              bool _3013_nullable = _3012___mcc_h25;
              bool _3014_referential = _3011___mcc_h24;
              {
                if (_3014_referential) {
                  if (_3013_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source105.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source105.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3015___mcc_h26 = _source105.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3016_op = _3015___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_3016_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source106 = _2985_op;
            if (_source106.is_Eq) {
              bool _3017___mcc_h27 = _source106.dtor_referential;
              bool _3018___mcc_h28 = _source106.dtor_nullable;
              bool _3019_nullable = _3018___mcc_h28;
              bool _3020_referential = _3017___mcc_h27;
              {
                if (_3020_referential) {
                  if (_3019_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source106.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source106.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3021___mcc_h29 = _source106.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3022_op = _3021___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_3022_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source107 = _2985_op;
            if (_source107.is_Eq) {
              bool _3023___mcc_h30 = _source107.dtor_referential;
              bool _3024___mcc_h31 = _source107.dtor_nullable;
              bool _3025_nullable = _3024___mcc_h31;
              bool _3026_referential = _3023___mcc_h30;
              {
                if (_3026_referential) {
                  if (_3025_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source107.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source107.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3027___mcc_h32 = _source107.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3028_op = _3027___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_3028_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source108 = _2985_op;
            if (_source108.is_Eq) {
              bool _3029___mcc_h33 = _source108.dtor_referential;
              bool _3030___mcc_h34 = _source108.dtor_nullable;
              bool _3031_nullable = _3030___mcc_h34;
              bool _3032_referential = _3029___mcc_h33;
              {
                if (_3032_referential) {
                  if (_3031_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source108.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source108.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3033___mcc_h35 = _source108.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3034_op = _3033___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_3034_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source109 = _2985_op;
            if (_source109.is_Eq) {
              bool _3035___mcc_h36 = _source109.dtor_referential;
              bool _3036___mcc_h37 = _source109.dtor_nullable;
              bool _3037_nullable = _3036___mcc_h37;
              bool _3038_referential = _3035___mcc_h36;
              {
                if (_3038_referential) {
                  if (_3037_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source109.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source109.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3039___mcc_h38 = _source109.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3040_op = _3039___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_3040_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source110 = _2985_op;
            if (_source110.is_Eq) {
              bool _3041___mcc_h39 = _source110.dtor_referential;
              bool _3042___mcc_h40 = _source110.dtor_nullable;
              bool _3043_nullable = _3042___mcc_h40;
              bool _3044_referential = _3041___mcc_h39;
              {
                if (_3044_referential) {
                  if (_3043_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source110.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source110.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3045___mcc_h41 = _source110.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3046_op = _3045___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_3046_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source111 = _2985_op;
            if (_source111.is_Eq) {
              bool _3047___mcc_h42 = _source111.dtor_referential;
              bool _3048___mcc_h43 = _source111.dtor_nullable;
              bool _3049_nullable = _3048___mcc_h43;
              bool _3050_referential = _3047___mcc_h42;
              {
                if (_3050_referential) {
                  if (_3049_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source111.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source111.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3051___mcc_h44 = _source111.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3052_op = _3051___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_3052_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source112 = _2985_op;
            if (_source112.is_Eq) {
              bool _3053___mcc_h45 = _source112.dtor_referential;
              bool _3054___mcc_h46 = _source112.dtor_nullable;
              bool _3055_nullable = _3054___mcc_h46;
              bool _3056_referential = _3053___mcc_h45;
              {
                if (_3056_referential) {
                  if (_3055_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source112.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source112.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3057___mcc_h47 = _source112.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3058_op = _3057___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_3058_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source113 = _2985_op;
            if (_source113.is_Eq) {
              bool _3059___mcc_h48 = _source113.dtor_referential;
              bool _3060___mcc_h49 = _source113.dtor_nullable;
              bool _3061_nullable = _3060___mcc_h49;
              bool _3062_referential = _3059___mcc_h48;
              {
                if (_3062_referential) {
                  if (_3061_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source113.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source113.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3063___mcc_h50 = _source113.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3064_op = _3063___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_3064_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source114 = _2985_op;
            if (_source114.is_Eq) {
              bool _3065___mcc_h51 = _source114.dtor_referential;
              bool _3066___mcc_h52 = _source114.dtor_nullable;
              bool _3067_nullable = _3066___mcc_h52;
              bool _3068_referential = _3065___mcc_h51;
              {
                if (_3068_referential) {
                  if (_3067_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source114.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source114.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3069___mcc_h53 = _source114.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3070_op = _3069___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_3070_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source115 = _2985_op;
            if (_source115.is_Eq) {
              bool _3071___mcc_h54 = _source115.dtor_referential;
              bool _3072___mcc_h55 = _source115.dtor_nullable;
              bool _3073_nullable = _3072___mcc_h55;
              bool _3074_referential = _3071___mcc_h54;
              {
                if (_3074_referential) {
                  if (_3073_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source115.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source115.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3075___mcc_h56 = _source115.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3076_op = _3075___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_3076_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source116 = _2985_op;
            if (_source116.is_Eq) {
              bool _3077___mcc_h57 = _source116.dtor_referential;
              bool _3078___mcc_h58 = _source116.dtor_nullable;
              bool _3079_nullable = _3078___mcc_h58;
              bool _3080_referential = _3077___mcc_h57;
              {
                if (_3080_referential) {
                  if (_3079_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source116.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source116.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3081___mcc_h59 = _source116.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3082_op = _3081___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_3082_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source117 = _2985_op;
            if (_source117.is_Eq) {
              bool _3083___mcc_h60 = _source117.dtor_referential;
              bool _3084___mcc_h61 = _source117.dtor_nullable;
              bool _3085_nullable = _3084___mcc_h61;
              bool _3086_referential = _3083___mcc_h60;
              {
                if (_3086_referential) {
                  if (_3085_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source117.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source117.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3087___mcc_h62 = _source117.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3088_op = _3087___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_3088_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source118 = _2985_op;
            if (_source118.is_Eq) {
              bool _3089___mcc_h63 = _source118.dtor_referential;
              bool _3090___mcc_h64 = _source118.dtor_nullable;
              bool _3091_nullable = _3090___mcc_h64;
              bool _3092_referential = _3089___mcc_h63;
              {
                if (_3092_referential) {
                  if (_3091_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source118.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source118.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3093___mcc_h65 = _source118.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3094_op = _3093___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_3094_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source119 = _2985_op;
            if (_source119.is_Eq) {
              bool _3095___mcc_h66 = _source119.dtor_referential;
              bool _3096___mcc_h67 = _source119.dtor_nullable;
              bool _3097_nullable = _3096___mcc_h67;
              bool _3098_referential = _3095___mcc_h66;
              {
                if (_3098_referential) {
                  if (_3097_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source119.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source119.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3099___mcc_h68 = _source119.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3100_op = _3099___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_3100_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source120 = _2985_op;
            if (_source120.is_Eq) {
              bool _3101___mcc_h69 = _source120.dtor_referential;
              bool _3102___mcc_h70 = _source120.dtor_nullable;
              bool _3103_nullable = _3102___mcc_h70;
              bool _3104_referential = _3101___mcc_h69;
              {
                if (_3104_referential) {
                  if (_3103_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source120.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source120.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3105___mcc_h71 = _source120.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3106_op = _3105___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_3106_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source121 = _2985_op;
            if (_source121.is_Eq) {
              bool _3107___mcc_h72 = _source121.dtor_referential;
              bool _3108___mcc_h73 = _source121.dtor_nullable;
              bool _3109_nullable = _3108___mcc_h73;
              bool _3110_referential = _3107___mcc_h72;
              {
                if (_3110_referential) {
                  if (_3109_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source121.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source121.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3111___mcc_h74 = _source121.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3112_op = _3111___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_3112_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      } else if (_source104.is_In) {
        {
          r = ((_3006_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_3003_left);
        }
      } else if (_source104.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3003_left, _3006_right, _2988_format);
      } else if (_source104.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3003_left, _3006_right, _2988_format);
      } else if (_source104.is_SetMerge) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3006_right);
        }
      } else if (_source104.is_SetSubtraction) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3006_right);
        }
      } else if (_source104.is_SetIntersection) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_3006_right);
        }
      } else if (_source104.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3003_left, _3006_right, _2988_format);
        }
      } else if (_source104.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3003_left, _3006_right, _2988_format);
        }
      } else if (_source104.is_SetDisjoint) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_3006_right);
        }
      } else if (_source104.is_MapMerge) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3006_right);
        }
      } else if (_source104.is_MapSubtraction) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3006_right);
        }
      } else if (_source104.is_MultisetMerge) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_3006_right);
        }
      } else if (_source104.is_MultisetSubtraction) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_3006_right);
        }
      } else if (_source104.is_MultisetIntersection) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_3006_right);
        }
      } else if (_source104.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _3003_left, _3006_right, _2988_format);
        }
      } else if (_source104.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _3003_left, _3006_right, _2988_format);
        }
      } else if (_source104.is_MultisetDisjoint) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_3006_right);
        }
      } else if (_source104.is_Concat) {
        {
          r = ((_3003_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_3006_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _3113___mcc_h22 = _source104.dtor_Passthrough_i_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2985_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2985_op), _3003_left, _3006_right, _2988_format);
          } else {
            DAST._IBinOp _source122 = _2985_op;
            if (_source122.is_Eq) {
              bool _3114___mcc_h75 = _source122.dtor_referential;
              bool _3115___mcc_h76 = _source122.dtor_nullable;
              bool _3116_nullable = _3115___mcc_h76;
              bool _3117_referential = _3114___mcc_h75;
              {
                if (_3117_referential) {
                  if (_3116_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _3003_left, _3006_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source122.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else if (_source122.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3003_left, _3006_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3118___mcc_h77 = _source122.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3119_op = _3118___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_3119_op, _3003_left, _3006_right, _2988_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out235;
      DCOMP._IOwnership _out236;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out235, out _out236);
      r = _out235;
      resultingOwnership = _out236;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3005_recIdentsL, _3008_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _3120_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _3121_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _3122_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _3123_recursiveGen;
      DCOMP._IOwnership _3124_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3125_recIdents;
      RAST._IExpr _out237;
      DCOMP._IOwnership _out238;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
      (this).GenExpr(_3120_expr, selfIdent, env, expectedOwnership, out _out237, out _out238, out _out239);
      _3123_recursiveGen = _out237;
      _3124_recOwned = _out238;
      _3125_recIdents = _out239;
      r = _3123_recursiveGen;
      if (object.Equals(_3124_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out240;
      DCOMP._IOwnership _out241;
      DCOMP.COMP.FromOwnership(r, _3124_recOwned, expectedOwnership, out _out240, out _out241);
      r = _out240;
      resultingOwnership = _out241;
      readIdents = _3125_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _3126_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _3127_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _3128_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _3129_recursiveGen;
      DCOMP._IOwnership _3130_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3131_recIdents;
      RAST._IExpr _out242;
      DCOMP._IOwnership _out243;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
      (this).GenExpr(_3126_expr, selfIdent, env, expectedOwnership, out _out242, out _out243, out _out244);
      _3129_recursiveGen = _out242;
      _3130_recOwned = _out243;
      _3131_recIdents = _out244;
      r = _3129_recursiveGen;
      if (object.Equals(_3130_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out245;
      DCOMP._IOwnership _out246;
      DCOMP.COMP.FromOwnership(r, _3130_recOwned, expectedOwnership, out _out245, out _out246);
      r = _out245;
      resultingOwnership = _out246;
      readIdents = _3131_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _3132_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _3133_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _3134_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _3134_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3135___v81 = _let_tmp_rhs56.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3136___v82 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _3137_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _3138_range = _let_tmp_rhs57.dtor_range;
      bool _3139_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3140_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3141_nativeToType;
      _3141_nativeToType = DCOMP.COMP.NewtypeToRustType(_3137_b, _3138_range);
      if (object.Equals(_3133_fromTpe, _3137_b)) {
        RAST._IExpr _3142_recursiveGen;
        DCOMP._IOwnership _3143_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3144_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_3132_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _3142_recursiveGen = _out247;
        _3143_recOwned = _out248;
        _3144_recIdents = _out249;
        readIdents = _3144_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source123 = _3141_nativeToType;
        if (_source123.is_None) {
          if (_3139_erase) {
            r = _3142_recursiveGen;
          } else {
            RAST._IType _3145_rhsType;
            RAST._IType _out250;
            _out250 = (this).GenType(_3134_toTpe, true, false);
            _3145_rhsType = _out250;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3145_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3142_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out251;
          DCOMP._IOwnership _out252;
          DCOMP.COMP.FromOwnership(r, _3143_recOwned, expectedOwnership, out _out251, out _out252);
          r = _out251;
          resultingOwnership = _out252;
        } else {
          RAST._IType _3146___mcc_h0 = _source123.dtor_value;
          RAST._IType _3147_v = _3146___mcc_h0;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3142_recursiveGen, RAST.Expr.create_ExprFromType(_3147_v)));
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_3141_nativeToType).is_Some) {
          DAST._IType _source124 = _3133_fromTpe;
          if (_source124.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3148___mcc_h1 = _source124.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3149___mcc_h2 = _source124.dtor_typeArgs;
            DAST._IResolvedType _3150___mcc_h3 = _source124.dtor_resolved;
            DAST._IResolvedType _source125 = _3150___mcc_h3;
            if (_source125.is_Datatype) {
              DAST._IDatatypeType _3151___mcc_h7 = _source125.dtor_datatypeType;
            } else if (_source125.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3152___mcc_h9 = _source125.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3153___mcc_h10 = _source125.dtor_attributes;
            } else {
              DAST._IType _3154___mcc_h13 = _source125.dtor_baseType;
              DAST._INewtypeRange _3155___mcc_h14 = _source125.dtor_range;
              bool _3156___mcc_h15 = _source125.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3157___mcc_h16 = _source125.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3158_attributes0 = _3157___mcc_h16;
              bool _3159_erase0 = _3156___mcc_h15;
              DAST._INewtypeRange _3160_range0 = _3155___mcc_h14;
              DAST._IType _3161_b0 = _3154___mcc_h13;
              {
                Std.Wrappers._IOption<RAST._IType> _3162_nativeFromType;
                _3162_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3161_b0, _3160_range0);
                if ((_3162_nativeFromType).is_Some) {
                  RAST._IExpr _3163_recursiveGen;
                  DCOMP._IOwnership _3164_recOwned;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3165_recIdents;
                  RAST._IExpr _out255;
                  DCOMP._IOwnership _out256;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
                  (this).GenExpr(_3132_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
                  _3163_recursiveGen = _out255;
                  _3164_recOwned = _out256;
                  _3165_recIdents = _out257;
                  RAST._IExpr _out258;
                  DCOMP._IOwnership _out259;
                  DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription(_3163_recursiveGen, (_3141_nativeToType).dtor_value), _3164_recOwned, expectedOwnership, out _out258, out _out259);
                  r = _out258;
                  resultingOwnership = _out259;
                  readIdents = _3165_recIdents;
                  return ;
                }
              }
            }
          } else if (_source124.is_Nullable) {
            DAST._IType _3166___mcc_h21 = _source124.dtor_Nullable_i_a0;
          } else if (_source124.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3167___mcc_h23 = _source124.dtor_Tuple_i_a0;
          } else if (_source124.is_Array) {
            DAST._IType _3168___mcc_h25 = _source124.dtor_element;
            BigInteger _3169___mcc_h26 = _source124.dtor_dims;
          } else if (_source124.is_Seq) {
            DAST._IType _3170___mcc_h29 = _source124.dtor_element;
          } else if (_source124.is_Set) {
            DAST._IType _3171___mcc_h31 = _source124.dtor_element;
          } else if (_source124.is_Multiset) {
            DAST._IType _3172___mcc_h33 = _source124.dtor_element;
          } else if (_source124.is_Map) {
            DAST._IType _3173___mcc_h35 = _source124.dtor_key;
            DAST._IType _3174___mcc_h36 = _source124.dtor_value;
          } else if (_source124.is_SetBuilder) {
            DAST._IType _3175___mcc_h39 = _source124.dtor_element;
          } else if (_source124.is_MapBuilder) {
            DAST._IType _3176___mcc_h41 = _source124.dtor_key;
            DAST._IType _3177___mcc_h42 = _source124.dtor_value;
          } else if (_source124.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3178___mcc_h45 = _source124.dtor_args;
            DAST._IType _3179___mcc_h46 = _source124.dtor_result;
          } else if (_source124.is_Primitive) {
            DAST._IPrimitive _3180___mcc_h49 = _source124.dtor_Primitive_i_a0;
          } else if (_source124.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3181___mcc_h51 = _source124.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _3182___mcc_h53 = _source124.dtor_TypeArg_i_a0;
          }
          if (object.Equals(_3133_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3183_recursiveGen;
            DCOMP._IOwnership _3184_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3185_recIdents;
            RAST._IExpr _out260;
            DCOMP._IOwnership _out261;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
            (this).GenExpr(_3132_expr, selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
            _3183_recursiveGen = _out260;
            _3184_recOwned = _out261;
            _3185_recIdents = _out262;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            DCOMP.COMP.FromOwnership(RAST.Expr.create_TypeAscription((_3183_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_3141_nativeToType).dtor_value), _3184_recOwned, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = _3185_recIdents;
            return ;
          }
        }
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3132_expr, _3133_fromTpe, _3137_b), _3137_b, _3134_toTpe), selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
        r = _out265;
        resultingOwnership = _out266;
        readIdents = _out267;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _3186_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _3187_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _3188_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _3187_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3189___v86 = _let_tmp_rhs59.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3190___v87 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _3191_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _3192_range = _let_tmp_rhs60.dtor_range;
      bool _3193_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3194_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3195_nativeFromType;
      _3195_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3191_b, _3192_range);
      if (object.Equals(_3191_b, _3188_toTpe)) {
        RAST._IExpr _3196_recursiveGen;
        DCOMP._IOwnership _3197_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3198_recIdents;
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(_3186_expr, selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
        _3196_recursiveGen = _out268;
        _3197_recOwned = _out269;
        _3198_recIdents = _out270;
        readIdents = _3198_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source126 = _3195_nativeFromType;
        if (_source126.is_None) {
          if (_3193_erase) {
            r = _3196_recursiveGen;
          } else {
            r = (_3196_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out271;
          DCOMP._IOwnership _out272;
          DCOMP.COMP.FromOwnership(r, _3197_recOwned, expectedOwnership, out _out271, out _out272);
          r = _out271;
          resultingOwnership = _out272;
        } else {
          RAST._IType _3199___mcc_h0 = _source126.dtor_value;
          RAST._IType _3200_v = _3199___mcc_h0;
          RAST._IType _3201_toTpeRust;
          RAST._IType _out273;
          _out273 = (this).GenType(_3188_toTpe, false, false);
          _3201_toTpeRust = _out273;
          r = (((_3196_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3201_toTpeRust))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out274;
          DCOMP._IOwnership _out275;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out274, out _out275);
          r = _out274;
          resultingOwnership = _out275;
        }
      } else {
        if ((_3195_nativeFromType).is_Some) {
          if (object.Equals(_3188_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3202_recursiveGen;
            DCOMP._IOwnership _3203_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3204_recIdents;
            RAST._IExpr _out276;
            DCOMP._IOwnership _out277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
            (this).GenExpr(_3186_expr, selfIdent, env, expectedOwnership, out _out276, out _out277, out _out278);
            _3202_recursiveGen = _out276;
            _3203_recOwned = _out277;
            _3204_recIdents = _out278;
            RAST._IExpr _out279;
            DCOMP._IOwnership _out280;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_3202_recursiveGen, (this).DafnyCharUnderlying)), _3203_recOwned, expectedOwnership, out _out279, out _out280);
            r = _out279;
            resultingOwnership = _out280;
            readIdents = _3204_recIdents;
            return ;
          }
        }
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3186_expr, _3187_fromTpe, _3191_b), _3191_b, _3188_toTpe), selfIdent, env, expectedOwnership, out _out281, out _out282, out _out283);
        r = _out281;
        resultingOwnership = _out282;
        readIdents = _out283;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _3205_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _3206_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _3207_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _3208_fromTpeGen;
      RAST._IType _out284;
      _out284 = (this).GenType(_3206_fromTpe, true, false);
      _3208_fromTpeGen = _out284;
      RAST._IType _3209_toTpeGen;
      RAST._IType _out285;
      _out285 = (this).GenType(_3207_toTpe, true, false);
      _3209_toTpeGen = _out285;
      RAST._IExpr _3210_recursiveGen;
      DCOMP._IOwnership _3211_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3212_recIdents;
      RAST._IExpr _out286;
      DCOMP._IOwnership _out287;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
      (this).GenExpr(_3205_expr, selfIdent, env, expectedOwnership, out _out286, out _out287, out _out288);
      _3210_recursiveGen = _out286;
      _3211_recOwned = _out287;
      _3212_recIdents = _out288;
      Dafny.ISequence<Dafny.Rune> _3213_msg;
      _3213_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_3208_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_3209_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_3213_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_3210_recursiveGen)._ToString(DCOMP.__default.IND), _3213_msg));
      RAST._IExpr _out289;
      DCOMP._IOwnership _out290;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out289, out _out290);
      r = _out289;
      resultingOwnership = _out290;
      readIdents = _3212_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _3214_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _3215_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _3216_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_3215_fromTpe, _3216_toTpe)) {
        RAST._IExpr _3217_recursiveGen;
        DCOMP._IOwnership _3218_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3219_recIdents;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
        (this).GenExpr(_3214_expr, selfIdent, env, expectedOwnership, out _out291, out _out292, out _out293);
        _3217_recursiveGen = _out291;
        _3218_recOwned = _out292;
        _3219_recIdents = _out293;
        r = _3217_recursiveGen;
        RAST._IExpr _out294;
        DCOMP._IOwnership _out295;
        DCOMP.COMP.FromOwnership(r, _3218_recOwned, expectedOwnership, out _out294, out _out295);
        r = _out294;
        resultingOwnership = _out295;
        readIdents = _3219_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source127 = _System.Tuple2<DAST._IType, DAST._IType>.create(_3215_fromTpe, _3216_toTpe);
        DAST._IType _3220___mcc_h0 = _source127.dtor__0;
        DAST._IType _3221___mcc_h1 = _source127.dtor__1;
        DAST._IType _source128 = _3220___mcc_h0;
        if (_source128.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3222___mcc_h4 = _source128.dtor_Path_i_a0;
          Dafny.ISequence<DAST._IType> _3223___mcc_h5 = _source128.dtor_typeArgs;
          DAST._IResolvedType _3224___mcc_h6 = _source128.dtor_resolved;
          DAST._IResolvedType _source129 = _3224___mcc_h6;
          if (_source129.is_Datatype) {
            DAST._IDatatypeType _3225___mcc_h16 = _source129.dtor_datatypeType;
            DAST._IType _source130 = _3221___mcc_h1;
            if (_source130.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3226___mcc_h20 = _source130.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3227___mcc_h21 = _source130.dtor_typeArgs;
              DAST._IResolvedType _3228___mcc_h22 = _source130.dtor_resolved;
              DAST._IResolvedType _source131 = _3228___mcc_h22;
              if (_source131.is_Datatype) {
                DAST._IDatatypeType _3229___mcc_h26 = _source131.dtor_datatypeType;
                {
                  RAST._IExpr _out296;
                  DCOMP._IOwnership _out297;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
                  r = _out296;
                  resultingOwnership = _out297;
                  readIdents = _out298;
                }
              } else if (_source131.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3230___mcc_h28 = _source131.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3231___mcc_h29 = _source131.dtor_attributes;
                {
                  RAST._IExpr _out299;
                  DCOMP._IOwnership _out300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out299, out _out300, out _out301);
                  r = _out299;
                  resultingOwnership = _out300;
                  readIdents = _out301;
                }
              } else {
                DAST._IType _3232___mcc_h32 = _source131.dtor_baseType;
                DAST._INewtypeRange _3233___mcc_h33 = _source131.dtor_range;
                bool _3234___mcc_h34 = _source131.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3235___mcc_h35 = _source131.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3236_attributes = _3235___mcc_h35;
                bool _3237_erase = _3234___mcc_h34;
                DAST._INewtypeRange _3238_range = _3233___mcc_h33;
                DAST._IType _3239_b = _3232___mcc_h32;
                {
                  RAST._IExpr _out302;
                  DCOMP._IOwnership _out303;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out302, out _out303, out _out304);
                  r = _out302;
                  resultingOwnership = _out303;
                  readIdents = _out304;
                }
              }
            } else if (_source130.is_Nullable) {
              DAST._IType _3240___mcc_h40 = _source130.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source130.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3241___mcc_h42 = _source130.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source130.is_Array) {
              DAST._IType _3242___mcc_h44 = _source130.dtor_element;
              BigInteger _3243___mcc_h45 = _source130.dtor_dims;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source130.is_Seq) {
              DAST._IType _3244___mcc_h48 = _source130.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source130.is_Set) {
              DAST._IType _3245___mcc_h50 = _source130.dtor_element;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source130.is_Multiset) {
              DAST._IType _3246___mcc_h52 = _source130.dtor_element;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source130.is_Map) {
              DAST._IType _3247___mcc_h54 = _source130.dtor_key;
              DAST._IType _3248___mcc_h55 = _source130.dtor_value;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source130.is_SetBuilder) {
              DAST._IType _3249___mcc_h58 = _source130.dtor_element;
              {
                RAST._IExpr _out326;
                DCOMP._IOwnership _out327;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out326, out _out327, out _out328);
                r = _out326;
                resultingOwnership = _out327;
                readIdents = _out328;
              }
            } else if (_source130.is_MapBuilder) {
              DAST._IType _3250___mcc_h60 = _source130.dtor_key;
              DAST._IType _3251___mcc_h61 = _source130.dtor_value;
              {
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out329, out _out330, out _out331);
                r = _out329;
                resultingOwnership = _out330;
                readIdents = _out331;
              }
            } else if (_source130.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3252___mcc_h64 = _source130.dtor_args;
              DAST._IType _3253___mcc_h65 = _source130.dtor_result;
              {
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out332, out _out333, out _out334);
                r = _out332;
                resultingOwnership = _out333;
                readIdents = _out334;
              }
            } else if (_source130.is_Primitive) {
              DAST._IPrimitive _3254___mcc_h68 = _source130.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out335;
                DCOMP._IOwnership _out336;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out335, out _out336, out _out337);
                r = _out335;
                resultingOwnership = _out336;
                readIdents = _out337;
              }
            } else if (_source130.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3255___mcc_h70 = _source130.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out338;
                DCOMP._IOwnership _out339;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out338, out _out339, out _out340);
                r = _out338;
                resultingOwnership = _out339;
                readIdents = _out340;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3256___mcc_h72 = _source130.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out341;
                DCOMP._IOwnership _out342;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out341, out _out342, out _out343);
                r = _out341;
                resultingOwnership = _out342;
                readIdents = _out343;
              }
            }
          } else if (_source129.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3257___mcc_h74 = _source129.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _3258___mcc_h75 = _source129.dtor_attributes;
            DAST._IType _source132 = _3221___mcc_h1;
            if (_source132.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3259___mcc_h82 = _source132.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3260___mcc_h83 = _source132.dtor_typeArgs;
              DAST._IResolvedType _3261___mcc_h84 = _source132.dtor_resolved;
              DAST._IResolvedType _source133 = _3261___mcc_h84;
              if (_source133.is_Datatype) {
                DAST._IDatatypeType _3262___mcc_h88 = _source133.dtor_datatypeType;
                {
                  RAST._IExpr _out344;
                  DCOMP._IOwnership _out345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out344, out _out345, out _out346);
                  r = _out344;
                  resultingOwnership = _out345;
                  readIdents = _out346;
                }
              } else if (_source133.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3263___mcc_h90 = _source133.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3264___mcc_h91 = _source133.dtor_attributes;
                {
                  RAST._IExpr _out347;
                  DCOMP._IOwnership _out348;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
                  r = _out347;
                  resultingOwnership = _out348;
                  readIdents = _out349;
                }
              } else {
                DAST._IType _3265___mcc_h94 = _source133.dtor_baseType;
                DAST._INewtypeRange _3266___mcc_h95 = _source133.dtor_range;
                bool _3267___mcc_h96 = _source133.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3268___mcc_h97 = _source133.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3269_attributes = _3268___mcc_h97;
                bool _3270_erase = _3267___mcc_h96;
                DAST._INewtypeRange _3271_range = _3266___mcc_h95;
                DAST._IType _3272_b = _3265___mcc_h94;
                {
                  RAST._IExpr _out350;
                  DCOMP._IOwnership _out351;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
                  r = _out350;
                  resultingOwnership = _out351;
                  readIdents = _out352;
                }
              }
            } else if (_source132.is_Nullable) {
              DAST._IType _3273___mcc_h102 = _source132.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source132.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3274___mcc_h104 = _source132.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source132.is_Array) {
              DAST._IType _3275___mcc_h106 = _source132.dtor_element;
              BigInteger _3276___mcc_h107 = _source132.dtor_dims;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source132.is_Seq) {
              DAST._IType _3277___mcc_h110 = _source132.dtor_element;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source132.is_Set) {
              DAST._IType _3278___mcc_h112 = _source132.dtor_element;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source132.is_Multiset) {
              DAST._IType _3279___mcc_h114 = _source132.dtor_element;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source132.is_Map) {
              DAST._IType _3280___mcc_h116 = _source132.dtor_key;
              DAST._IType _3281___mcc_h117 = _source132.dtor_value;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source132.is_SetBuilder) {
              DAST._IType _3282___mcc_h120 = _source132.dtor_element;
              {
                RAST._IExpr _out374;
                DCOMP._IOwnership _out375;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out374, out _out375, out _out376);
                r = _out374;
                resultingOwnership = _out375;
                readIdents = _out376;
              }
            } else if (_source132.is_MapBuilder) {
              DAST._IType _3283___mcc_h122 = _source132.dtor_key;
              DAST._IType _3284___mcc_h123 = _source132.dtor_value;
              {
                RAST._IExpr _out377;
                DCOMP._IOwnership _out378;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out377, out _out378, out _out379);
                r = _out377;
                resultingOwnership = _out378;
                readIdents = _out379;
              }
            } else if (_source132.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3285___mcc_h126 = _source132.dtor_args;
              DAST._IType _3286___mcc_h127 = _source132.dtor_result;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source132.is_Primitive) {
              DAST._IPrimitive _3287___mcc_h130 = _source132.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out383;
                DCOMP._IOwnership _out384;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out383, out _out384, out _out385);
                r = _out383;
                resultingOwnership = _out384;
                readIdents = _out385;
              }
            } else if (_source132.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3288___mcc_h132 = _source132.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out386;
                DCOMP._IOwnership _out387;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out386, out _out387, out _out388);
                r = _out386;
                resultingOwnership = _out387;
                readIdents = _out388;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3289___mcc_h134 = _source132.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out389;
                DCOMP._IOwnership _out390;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out389, out _out390, out _out391);
                r = _out389;
                resultingOwnership = _out390;
                readIdents = _out391;
              }
            }
          } else {
            DAST._IType _3290___mcc_h136 = _source129.dtor_baseType;
            DAST._INewtypeRange _3291___mcc_h137 = _source129.dtor_range;
            bool _3292___mcc_h138 = _source129.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _3293___mcc_h139 = _source129.dtor_attributes;
            DAST._IType _source134 = _3221___mcc_h1;
            if (_source134.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3294___mcc_h152 = _source134.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3295___mcc_h153 = _source134.dtor_typeArgs;
              DAST._IResolvedType _3296___mcc_h154 = _source134.dtor_resolved;
              DAST._IResolvedType _source135 = _3296___mcc_h154;
              if (_source135.is_Datatype) {
                DAST._IDatatypeType _3297___mcc_h161 = _source135.dtor_datatypeType;
                Dafny.ISequence<DAST._IAttribute> _3298_attributes = _3293___mcc_h139;
                bool _3299_erase = _3292___mcc_h138;
                DAST._INewtypeRange _3300_range = _3291___mcc_h137;
                DAST._IType _3301_b = _3290___mcc_h136;
                {
                  RAST._IExpr _out392;
                  DCOMP._IOwnership _out393;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out392, out _out393, out _out394);
                  r = _out392;
                  resultingOwnership = _out393;
                  readIdents = _out394;
                }
              } else if (_source135.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3302___mcc_h164 = _source135.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3303___mcc_h165 = _source135.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3304_attributes = _3293___mcc_h139;
                bool _3305_erase = _3292___mcc_h138;
                DAST._INewtypeRange _3306_range = _3291___mcc_h137;
                DAST._IType _3307_b = _3290___mcc_h136;
                {
                  RAST._IExpr _out395;
                  DCOMP._IOwnership _out396;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out395, out _out396, out _out397);
                  r = _out395;
                  resultingOwnership = _out396;
                  readIdents = _out397;
                }
              } else {
                DAST._IType _3308___mcc_h170 = _source135.dtor_baseType;
                DAST._INewtypeRange _3309___mcc_h171 = _source135.dtor_range;
                bool _3310___mcc_h172 = _source135.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3311___mcc_h173 = _source135.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3312_attributes = _3311___mcc_h173;
                bool _3313_erase = _3310___mcc_h172;
                DAST._INewtypeRange _3314_range = _3309___mcc_h171;
                DAST._IType _3315_b = _3308___mcc_h170;
                {
                  RAST._IExpr _out398;
                  DCOMP._IOwnership _out399;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out398, out _out399, out _out400);
                  r = _out398;
                  resultingOwnership = _out399;
                  readIdents = _out400;
                }
              }
            } else if (_source134.is_Nullable) {
              DAST._IType _3316___mcc_h182 = _source134.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out401;
                DCOMP._IOwnership _out402;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out401, out _out402, out _out403);
                r = _out401;
                resultingOwnership = _out402;
                readIdents = _out403;
              }
            } else if (_source134.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3317___mcc_h185 = _source134.dtor_Tuple_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3318_attributes = _3293___mcc_h139;
              bool _3319_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3320_range = _3291___mcc_h137;
              DAST._IType _3321_b = _3290___mcc_h136;
              {
                RAST._IExpr _out404;
                DCOMP._IOwnership _out405;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out404, out _out405, out _out406);
                r = _out404;
                resultingOwnership = _out405;
                readIdents = _out406;
              }
            } else if (_source134.is_Array) {
              DAST._IType _3322___mcc_h188 = _source134.dtor_element;
              BigInteger _3323___mcc_h189 = _source134.dtor_dims;
              Dafny.ISequence<DAST._IAttribute> _3324_attributes = _3293___mcc_h139;
              bool _3325_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3326_range = _3291___mcc_h137;
              DAST._IType _3327_b = _3290___mcc_h136;
              {
                RAST._IExpr _out407;
                DCOMP._IOwnership _out408;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out407, out _out408, out _out409);
                r = _out407;
                resultingOwnership = _out408;
                readIdents = _out409;
              }
            } else if (_source134.is_Seq) {
              DAST._IType _3328___mcc_h194 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3329_attributes = _3293___mcc_h139;
              bool _3330_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3331_range = _3291___mcc_h137;
              DAST._IType _3332_b = _3290___mcc_h136;
              {
                RAST._IExpr _out410;
                DCOMP._IOwnership _out411;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out410, out _out411, out _out412);
                r = _out410;
                resultingOwnership = _out411;
                readIdents = _out412;
              }
            } else if (_source134.is_Set) {
              DAST._IType _3333___mcc_h197 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3334_attributes = _3293___mcc_h139;
              bool _3335_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3336_range = _3291___mcc_h137;
              DAST._IType _3337_b = _3290___mcc_h136;
              {
                RAST._IExpr _out413;
                DCOMP._IOwnership _out414;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out413, out _out414, out _out415);
                r = _out413;
                resultingOwnership = _out414;
                readIdents = _out415;
              }
            } else if (_source134.is_Multiset) {
              DAST._IType _3338___mcc_h200 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3339_attributes = _3293___mcc_h139;
              bool _3340_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3341_range = _3291___mcc_h137;
              DAST._IType _3342_b = _3290___mcc_h136;
              {
                RAST._IExpr _out416;
                DCOMP._IOwnership _out417;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out416, out _out417, out _out418);
                r = _out416;
                resultingOwnership = _out417;
                readIdents = _out418;
              }
            } else if (_source134.is_Map) {
              DAST._IType _3343___mcc_h203 = _source134.dtor_key;
              DAST._IType _3344___mcc_h204 = _source134.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3345_attributes = _3293___mcc_h139;
              bool _3346_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3347_range = _3291___mcc_h137;
              DAST._IType _3348_b = _3290___mcc_h136;
              {
                RAST._IExpr _out419;
                DCOMP._IOwnership _out420;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out419, out _out420, out _out421);
                r = _out419;
                resultingOwnership = _out420;
                readIdents = _out421;
              }
            } else if (_source134.is_SetBuilder) {
              DAST._IType _3349___mcc_h209 = _source134.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3350_attributes = _3293___mcc_h139;
              bool _3351_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3352_range = _3291___mcc_h137;
              DAST._IType _3353_b = _3290___mcc_h136;
              {
                RAST._IExpr _out422;
                DCOMP._IOwnership _out423;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out422, out _out423, out _out424);
                r = _out422;
                resultingOwnership = _out423;
                readIdents = _out424;
              }
            } else if (_source134.is_MapBuilder) {
              DAST._IType _3354___mcc_h212 = _source134.dtor_key;
              DAST._IType _3355___mcc_h213 = _source134.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3356_attributes = _3293___mcc_h139;
              bool _3357_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3358_range = _3291___mcc_h137;
              DAST._IType _3359_b = _3290___mcc_h136;
              {
                RAST._IExpr _out425;
                DCOMP._IOwnership _out426;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out425, out _out426, out _out427);
                r = _out425;
                resultingOwnership = _out426;
                readIdents = _out427;
              }
            } else if (_source134.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3360___mcc_h218 = _source134.dtor_args;
              DAST._IType _3361___mcc_h219 = _source134.dtor_result;
              Dafny.ISequence<DAST._IAttribute> _3362_attributes = _3293___mcc_h139;
              bool _3363_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3364_range = _3291___mcc_h137;
              DAST._IType _3365_b = _3290___mcc_h136;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source134.is_Primitive) {
              DAST._IPrimitive _3366___mcc_h224 = _source134.dtor_Primitive_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3367_attributes = _3293___mcc_h139;
              bool _3368_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3369_range = _3291___mcc_h137;
              DAST._IType _3370_b = _3290___mcc_h136;
              {
                RAST._IExpr _out431;
                DCOMP._IOwnership _out432;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out431, out _out432, out _out433);
                r = _out431;
                resultingOwnership = _out432;
                readIdents = _out433;
              }
            } else if (_source134.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3371___mcc_h227 = _source134.dtor_Passthrough_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3372_attributes = _3293___mcc_h139;
              bool _3373_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3374_range = _3291___mcc_h137;
              DAST._IType _3375_b = _3290___mcc_h136;
              {
                RAST._IExpr _out434;
                DCOMP._IOwnership _out435;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out434, out _out435, out _out436);
                r = _out434;
                resultingOwnership = _out435;
                readIdents = _out436;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3376___mcc_h230 = _source134.dtor_TypeArg_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3377_attributes = _3293___mcc_h139;
              bool _3378_erase = _3292___mcc_h138;
              DAST._INewtypeRange _3379_range = _3291___mcc_h137;
              DAST._IType _3380_b = _3290___mcc_h136;
              {
                RAST._IExpr _out437;
                DCOMP._IOwnership _out438;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out437, out _out438, out _out439);
                r = _out437;
                resultingOwnership = _out438;
                readIdents = _out439;
              }
            }
          }
        } else if (_source128.is_Nullable) {
          DAST._IType _3381___mcc_h233 = _source128.dtor_Nullable_i_a0;
          DAST._IType _source136 = _3221___mcc_h1;
          if (_source136.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3382___mcc_h237 = _source136.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3383___mcc_h238 = _source136.dtor_typeArgs;
            DAST._IResolvedType _3384___mcc_h239 = _source136.dtor_resolved;
            DAST._IResolvedType _source137 = _3384___mcc_h239;
            if (_source137.is_Datatype) {
              DAST._IDatatypeType _3385___mcc_h246 = _source137.dtor_datatypeType;
              {
                RAST._IExpr _out440;
                DCOMP._IOwnership _out441;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out440, out _out441, out _out442);
                r = _out440;
                resultingOwnership = _out441;
                readIdents = _out442;
              }
            } else if (_source137.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3386___mcc_h249 = _source137.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3387___mcc_h250 = _source137.dtor_attributes;
              {
                RAST._IExpr _out443;
                DCOMP._IOwnership _out444;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out443, out _out444, out _out445);
                r = _out443;
                resultingOwnership = _out444;
                readIdents = _out445;
              }
            } else {
              DAST._IType _3388___mcc_h255 = _source137.dtor_baseType;
              DAST._INewtypeRange _3389___mcc_h256 = _source137.dtor_range;
              bool _3390___mcc_h257 = _source137.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3391___mcc_h258 = _source137.dtor_attributes;
              {
                RAST._IExpr _out446;
                DCOMP._IOwnership _out447;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out446, out _out447, out _out448);
                r = _out446;
                resultingOwnership = _out447;
                readIdents = _out448;
              }
            }
          } else if (_source136.is_Nullable) {
            DAST._IType _3392___mcc_h267 = _source136.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source136.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3393___mcc_h270 = _source136.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source136.is_Array) {
            DAST._IType _3394___mcc_h273 = _source136.dtor_element;
            BigInteger _3395___mcc_h274 = _source136.dtor_dims;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source136.is_Seq) {
            DAST._IType _3396___mcc_h279 = _source136.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source136.is_Set) {
            DAST._IType _3397___mcc_h282 = _source136.dtor_element;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source136.is_Multiset) {
            DAST._IType _3398___mcc_h285 = _source136.dtor_element;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source136.is_Map) {
            DAST._IType _3399___mcc_h288 = _source136.dtor_key;
            DAST._IType _3400___mcc_h289 = _source136.dtor_value;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source136.is_SetBuilder) {
            DAST._IType _3401___mcc_h294 = _source136.dtor_element;
            {
              RAST._IExpr _out470;
              DCOMP._IOwnership _out471;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out470, out _out471, out _out472);
              r = _out470;
              resultingOwnership = _out471;
              readIdents = _out472;
            }
          } else if (_source136.is_MapBuilder) {
            DAST._IType _3402___mcc_h297 = _source136.dtor_key;
            DAST._IType _3403___mcc_h298 = _source136.dtor_value;
            {
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out473, out _out474, out _out475);
              r = _out473;
              resultingOwnership = _out474;
              readIdents = _out475;
            }
          } else if (_source136.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3404___mcc_h303 = _source136.dtor_args;
            DAST._IType _3405___mcc_h304 = _source136.dtor_result;
            {
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out476, out _out477, out _out478);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _out478;
            }
          } else if (_source136.is_Primitive) {
            DAST._IPrimitive _3406___mcc_h309 = _source136.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out479, out _out480, out _out481);
              r = _out479;
              resultingOwnership = _out480;
              readIdents = _out481;
            }
          } else if (_source136.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3407___mcc_h312 = _source136.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out482, out _out483, out _out484);
              r = _out482;
              resultingOwnership = _out483;
              readIdents = _out484;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3408___mcc_h315 = _source136.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out485, out _out486, out _out487);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _out487;
            }
          }
        } else if (_source128.is_Tuple) {
          Dafny.ISequence<DAST._IType> _3409___mcc_h318 = _source128.dtor_Tuple_i_a0;
          DAST._IType _source138 = _3221___mcc_h1;
          if (_source138.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3410___mcc_h322 = _source138.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3411___mcc_h323 = _source138.dtor_typeArgs;
            DAST._IResolvedType _3412___mcc_h324 = _source138.dtor_resolved;
            DAST._IResolvedType _source139 = _3412___mcc_h324;
            if (_source139.is_Datatype) {
              DAST._IDatatypeType _3413___mcc_h328 = _source139.dtor_datatypeType;
              {
                RAST._IExpr _out488;
                DCOMP._IOwnership _out489;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
                r = _out488;
                resultingOwnership = _out489;
                readIdents = _out490;
              }
            } else if (_source139.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3414___mcc_h330 = _source139.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3415___mcc_h331 = _source139.dtor_attributes;
              {
                RAST._IExpr _out491;
                DCOMP._IOwnership _out492;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out491, out _out492, out _out493);
                r = _out491;
                resultingOwnership = _out492;
                readIdents = _out493;
              }
            } else {
              DAST._IType _3416___mcc_h334 = _source139.dtor_baseType;
              DAST._INewtypeRange _3417___mcc_h335 = _source139.dtor_range;
              bool _3418___mcc_h336 = _source139.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3419___mcc_h337 = _source139.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3420_attributes = _3419___mcc_h337;
              bool _3421_erase = _3418___mcc_h336;
              DAST._INewtypeRange _3422_range = _3417___mcc_h335;
              DAST._IType _3423_b = _3416___mcc_h334;
              {
                RAST._IExpr _out494;
                DCOMP._IOwnership _out495;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out494, out _out495, out _out496);
                r = _out494;
                resultingOwnership = _out495;
                readIdents = _out496;
              }
            }
          } else if (_source138.is_Nullable) {
            DAST._IType _3424___mcc_h342 = _source138.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source138.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3425___mcc_h344 = _source138.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source138.is_Array) {
            DAST._IType _3426___mcc_h346 = _source138.dtor_element;
            BigInteger _3427___mcc_h347 = _source138.dtor_dims;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source138.is_Seq) {
            DAST._IType _3428___mcc_h350 = _source138.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source138.is_Set) {
            DAST._IType _3429___mcc_h352 = _source138.dtor_element;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source138.is_Multiset) {
            DAST._IType _3430___mcc_h354 = _source138.dtor_element;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source138.is_Map) {
            DAST._IType _3431___mcc_h356 = _source138.dtor_key;
            DAST._IType _3432___mcc_h357 = _source138.dtor_value;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source138.is_SetBuilder) {
            DAST._IType _3433___mcc_h360 = _source138.dtor_element;
            {
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out518, out _out519, out _out520);
              r = _out518;
              resultingOwnership = _out519;
              readIdents = _out520;
            }
          } else if (_source138.is_MapBuilder) {
            DAST._IType _3434___mcc_h362 = _source138.dtor_key;
            DAST._IType _3435___mcc_h363 = _source138.dtor_value;
            {
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out523;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out521, out _out522, out _out523);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _out523;
            }
          } else if (_source138.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3436___mcc_h366 = _source138.dtor_args;
            DAST._IType _3437___mcc_h367 = _source138.dtor_result;
            {
              RAST._IExpr _out524;
              DCOMP._IOwnership _out525;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out524, out _out525, out _out526);
              r = _out524;
              resultingOwnership = _out525;
              readIdents = _out526;
            }
          } else if (_source138.is_Primitive) {
            DAST._IPrimitive _3438___mcc_h370 = _source138.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out527;
              DCOMP._IOwnership _out528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out527, out _out528, out _out529);
              r = _out527;
              resultingOwnership = _out528;
              readIdents = _out529;
            }
          } else if (_source138.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3439___mcc_h372 = _source138.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out530, out _out531, out _out532);
              r = _out530;
              resultingOwnership = _out531;
              readIdents = _out532;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3440___mcc_h374 = _source138.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out533, out _out534, out _out535);
              r = _out533;
              resultingOwnership = _out534;
              readIdents = _out535;
            }
          }
        } else if (_source128.is_Array) {
          DAST._IType _3441___mcc_h376 = _source128.dtor_element;
          BigInteger _3442___mcc_h377 = _source128.dtor_dims;
          DAST._IType _source140 = _3221___mcc_h1;
          if (_source140.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3443___mcc_h384 = _source140.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3444___mcc_h385 = _source140.dtor_typeArgs;
            DAST._IResolvedType _3445___mcc_h386 = _source140.dtor_resolved;
            DAST._IResolvedType _source141 = _3445___mcc_h386;
            if (_source141.is_Datatype) {
              DAST._IDatatypeType _3446___mcc_h390 = _source141.dtor_datatypeType;
              {
                RAST._IExpr _out536;
                DCOMP._IOwnership _out537;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out536, out _out537, out _out538);
                r = _out536;
                resultingOwnership = _out537;
                readIdents = _out538;
              }
            } else if (_source141.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3447___mcc_h392 = _source141.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3448___mcc_h393 = _source141.dtor_attributes;
              {
                RAST._IExpr _out539;
                DCOMP._IOwnership _out540;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out539, out _out540, out _out541);
                r = _out539;
                resultingOwnership = _out540;
                readIdents = _out541;
              }
            } else {
              DAST._IType _3449___mcc_h396 = _source141.dtor_baseType;
              DAST._INewtypeRange _3450___mcc_h397 = _source141.dtor_range;
              bool _3451___mcc_h398 = _source141.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3452___mcc_h399 = _source141.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3453_attributes = _3452___mcc_h399;
              bool _3454_erase = _3451___mcc_h398;
              DAST._INewtypeRange _3455_range = _3450___mcc_h397;
              DAST._IType _3456_b = _3449___mcc_h396;
              {
                RAST._IExpr _out542;
                DCOMP._IOwnership _out543;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out542, out _out543, out _out544);
                r = _out542;
                resultingOwnership = _out543;
                readIdents = _out544;
              }
            }
          } else if (_source140.is_Nullable) {
            DAST._IType _3457___mcc_h404 = _source140.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source140.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3458___mcc_h406 = _source140.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source140.is_Array) {
            DAST._IType _3459___mcc_h408 = _source140.dtor_element;
            BigInteger _3460___mcc_h409 = _source140.dtor_dims;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source140.is_Seq) {
            DAST._IType _3461___mcc_h412 = _source140.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source140.is_Set) {
            DAST._IType _3462___mcc_h414 = _source140.dtor_element;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source140.is_Multiset) {
            DAST._IType _3463___mcc_h416 = _source140.dtor_element;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source140.is_Map) {
            DAST._IType _3464___mcc_h418 = _source140.dtor_key;
            DAST._IType _3465___mcc_h419 = _source140.dtor_value;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source140.is_SetBuilder) {
            DAST._IType _3466___mcc_h422 = _source140.dtor_element;
            {
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out566, out _out567, out _out568);
              r = _out566;
              resultingOwnership = _out567;
              readIdents = _out568;
            }
          } else if (_source140.is_MapBuilder) {
            DAST._IType _3467___mcc_h424 = _source140.dtor_key;
            DAST._IType _3468___mcc_h425 = _source140.dtor_value;
            {
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out569, out _out570, out _out571);
              r = _out569;
              resultingOwnership = _out570;
              readIdents = _out571;
            }
          } else if (_source140.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3469___mcc_h428 = _source140.dtor_args;
            DAST._IType _3470___mcc_h429 = _source140.dtor_result;
            {
              RAST._IExpr _out572;
              DCOMP._IOwnership _out573;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out572, out _out573, out _out574);
              r = _out572;
              resultingOwnership = _out573;
              readIdents = _out574;
            }
          } else if (_source140.is_Primitive) {
            DAST._IPrimitive _3471___mcc_h432 = _source140.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out575;
              DCOMP._IOwnership _out576;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out575, out _out576, out _out577);
              r = _out575;
              resultingOwnership = _out576;
              readIdents = _out577;
            }
          } else if (_source140.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3472___mcc_h434 = _source140.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out578;
              DCOMP._IOwnership _out579;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out578, out _out579, out _out580);
              r = _out578;
              resultingOwnership = _out579;
              readIdents = _out580;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3473___mcc_h436 = _source140.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out581;
              DCOMP._IOwnership _out582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out583;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out581, out _out582, out _out583);
              r = _out581;
              resultingOwnership = _out582;
              readIdents = _out583;
            }
          }
        } else if (_source128.is_Seq) {
          DAST._IType _3474___mcc_h438 = _source128.dtor_element;
          DAST._IType _source142 = _3221___mcc_h1;
          if (_source142.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3475___mcc_h442 = _source142.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3476___mcc_h443 = _source142.dtor_typeArgs;
            DAST._IResolvedType _3477___mcc_h444 = _source142.dtor_resolved;
            DAST._IResolvedType _source143 = _3477___mcc_h444;
            if (_source143.is_Datatype) {
              DAST._IDatatypeType _3478___mcc_h448 = _source143.dtor_datatypeType;
              {
                RAST._IExpr _out584;
                DCOMP._IOwnership _out585;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out584, out _out585, out _out586);
                r = _out584;
                resultingOwnership = _out585;
                readIdents = _out586;
              }
            } else if (_source143.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3479___mcc_h450 = _source143.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3480___mcc_h451 = _source143.dtor_attributes;
              {
                RAST._IExpr _out587;
                DCOMP._IOwnership _out588;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out587, out _out588, out _out589);
                r = _out587;
                resultingOwnership = _out588;
                readIdents = _out589;
              }
            } else {
              DAST._IType _3481___mcc_h454 = _source143.dtor_baseType;
              DAST._INewtypeRange _3482___mcc_h455 = _source143.dtor_range;
              bool _3483___mcc_h456 = _source143.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3484___mcc_h457 = _source143.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3485_attributes = _3484___mcc_h457;
              bool _3486_erase = _3483___mcc_h456;
              DAST._INewtypeRange _3487_range = _3482___mcc_h455;
              DAST._IType _3488_b = _3481___mcc_h454;
              {
                RAST._IExpr _out590;
                DCOMP._IOwnership _out591;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out590, out _out591, out _out592);
                r = _out590;
                resultingOwnership = _out591;
                readIdents = _out592;
              }
            }
          } else if (_source142.is_Nullable) {
            DAST._IType _3489___mcc_h462 = _source142.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source142.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3490___mcc_h464 = _source142.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source142.is_Array) {
            DAST._IType _3491___mcc_h466 = _source142.dtor_element;
            BigInteger _3492___mcc_h467 = _source142.dtor_dims;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source142.is_Seq) {
            DAST._IType _3493___mcc_h470 = _source142.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source142.is_Set) {
            DAST._IType _3494___mcc_h472 = _source142.dtor_element;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source142.is_Multiset) {
            DAST._IType _3495___mcc_h474 = _source142.dtor_element;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source142.is_Map) {
            DAST._IType _3496___mcc_h476 = _source142.dtor_key;
            DAST._IType _3497___mcc_h477 = _source142.dtor_value;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source142.is_SetBuilder) {
            DAST._IType _3498___mcc_h480 = _source142.dtor_element;
            {
              RAST._IExpr _out614;
              DCOMP._IOwnership _out615;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out614, out _out615, out _out616);
              r = _out614;
              resultingOwnership = _out615;
              readIdents = _out616;
            }
          } else if (_source142.is_MapBuilder) {
            DAST._IType _3499___mcc_h482 = _source142.dtor_key;
            DAST._IType _3500___mcc_h483 = _source142.dtor_value;
            {
              RAST._IExpr _out617;
              DCOMP._IOwnership _out618;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out617, out _out618, out _out619);
              r = _out617;
              resultingOwnership = _out618;
              readIdents = _out619;
            }
          } else if (_source142.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3501___mcc_h486 = _source142.dtor_args;
            DAST._IType _3502___mcc_h487 = _source142.dtor_result;
            {
              RAST._IExpr _out620;
              DCOMP._IOwnership _out621;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out620, out _out621, out _out622);
              r = _out620;
              resultingOwnership = _out621;
              readIdents = _out622;
            }
          } else if (_source142.is_Primitive) {
            DAST._IPrimitive _3503___mcc_h490 = _source142.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out623, out _out624, out _out625);
              r = _out623;
              resultingOwnership = _out624;
              readIdents = _out625;
            }
          } else if (_source142.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3504___mcc_h492 = _source142.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out626;
              DCOMP._IOwnership _out627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out628;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out626, out _out627, out _out628);
              r = _out626;
              resultingOwnership = _out627;
              readIdents = _out628;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3505___mcc_h494 = _source142.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out629;
              DCOMP._IOwnership _out630;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out629, out _out630, out _out631);
              r = _out629;
              resultingOwnership = _out630;
              readIdents = _out631;
            }
          }
        } else if (_source128.is_Set) {
          DAST._IType _3506___mcc_h496 = _source128.dtor_element;
          DAST._IType _source144 = _3221___mcc_h1;
          if (_source144.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3507___mcc_h500 = _source144.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3508___mcc_h501 = _source144.dtor_typeArgs;
            DAST._IResolvedType _3509___mcc_h502 = _source144.dtor_resolved;
            DAST._IResolvedType _source145 = _3509___mcc_h502;
            if (_source145.is_Datatype) {
              DAST._IDatatypeType _3510___mcc_h506 = _source145.dtor_datatypeType;
              {
                RAST._IExpr _out632;
                DCOMP._IOwnership _out633;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out632, out _out633, out _out634);
                r = _out632;
                resultingOwnership = _out633;
                readIdents = _out634;
              }
            } else if (_source145.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3511___mcc_h508 = _source145.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3512___mcc_h509 = _source145.dtor_attributes;
              {
                RAST._IExpr _out635;
                DCOMP._IOwnership _out636;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out635, out _out636, out _out637);
                r = _out635;
                resultingOwnership = _out636;
                readIdents = _out637;
              }
            } else {
              DAST._IType _3513___mcc_h512 = _source145.dtor_baseType;
              DAST._INewtypeRange _3514___mcc_h513 = _source145.dtor_range;
              bool _3515___mcc_h514 = _source145.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3516___mcc_h515 = _source145.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3517_attributes = _3516___mcc_h515;
              bool _3518_erase = _3515___mcc_h514;
              DAST._INewtypeRange _3519_range = _3514___mcc_h513;
              DAST._IType _3520_b = _3513___mcc_h512;
              {
                RAST._IExpr _out638;
                DCOMP._IOwnership _out639;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out638, out _out639, out _out640);
                r = _out638;
                resultingOwnership = _out639;
                readIdents = _out640;
              }
            }
          } else if (_source144.is_Nullable) {
            DAST._IType _3521___mcc_h520 = _source144.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source144.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3522___mcc_h522 = _source144.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source144.is_Array) {
            DAST._IType _3523___mcc_h524 = _source144.dtor_element;
            BigInteger _3524___mcc_h525 = _source144.dtor_dims;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source144.is_Seq) {
            DAST._IType _3525___mcc_h528 = _source144.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source144.is_Set) {
            DAST._IType _3526___mcc_h530 = _source144.dtor_element;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source144.is_Multiset) {
            DAST._IType _3527___mcc_h532 = _source144.dtor_element;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source144.is_Map) {
            DAST._IType _3528___mcc_h534 = _source144.dtor_key;
            DAST._IType _3529___mcc_h535 = _source144.dtor_value;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source144.is_SetBuilder) {
            DAST._IType _3530___mcc_h538 = _source144.dtor_element;
            {
              RAST._IExpr _out662;
              DCOMP._IOwnership _out663;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out662, out _out663, out _out664);
              r = _out662;
              resultingOwnership = _out663;
              readIdents = _out664;
            }
          } else if (_source144.is_MapBuilder) {
            DAST._IType _3531___mcc_h540 = _source144.dtor_key;
            DAST._IType _3532___mcc_h541 = _source144.dtor_value;
            {
              RAST._IExpr _out665;
              DCOMP._IOwnership _out666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out665, out _out666, out _out667);
              r = _out665;
              resultingOwnership = _out666;
              readIdents = _out667;
            }
          } else if (_source144.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3533___mcc_h544 = _source144.dtor_args;
            DAST._IType _3534___mcc_h545 = _source144.dtor_result;
            {
              RAST._IExpr _out668;
              DCOMP._IOwnership _out669;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out668, out _out669, out _out670);
              r = _out668;
              resultingOwnership = _out669;
              readIdents = _out670;
            }
          } else if (_source144.is_Primitive) {
            DAST._IPrimitive _3535___mcc_h548 = _source144.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out671;
              DCOMP._IOwnership _out672;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out673;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out671, out _out672, out _out673);
              r = _out671;
              resultingOwnership = _out672;
              readIdents = _out673;
            }
          } else if (_source144.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3536___mcc_h550 = _source144.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out674;
              DCOMP._IOwnership _out675;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out676;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out674, out _out675, out _out676);
              r = _out674;
              resultingOwnership = _out675;
              readIdents = _out676;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3537___mcc_h552 = _source144.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out677;
              DCOMP._IOwnership _out678;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out677, out _out678, out _out679);
              r = _out677;
              resultingOwnership = _out678;
              readIdents = _out679;
            }
          }
        } else if (_source128.is_Multiset) {
          DAST._IType _3538___mcc_h554 = _source128.dtor_element;
          DAST._IType _source146 = _3221___mcc_h1;
          if (_source146.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3539___mcc_h558 = _source146.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3540___mcc_h559 = _source146.dtor_typeArgs;
            DAST._IResolvedType _3541___mcc_h560 = _source146.dtor_resolved;
            DAST._IResolvedType _source147 = _3541___mcc_h560;
            if (_source147.is_Datatype) {
              DAST._IDatatypeType _3542___mcc_h564 = _source147.dtor_datatypeType;
              {
                RAST._IExpr _out680;
                DCOMP._IOwnership _out681;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out680, out _out681, out _out682);
                r = _out680;
                resultingOwnership = _out681;
                readIdents = _out682;
              }
            } else if (_source147.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3543___mcc_h566 = _source147.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3544___mcc_h567 = _source147.dtor_attributes;
              {
                RAST._IExpr _out683;
                DCOMP._IOwnership _out684;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out683, out _out684, out _out685);
                r = _out683;
                resultingOwnership = _out684;
                readIdents = _out685;
              }
            } else {
              DAST._IType _3545___mcc_h570 = _source147.dtor_baseType;
              DAST._INewtypeRange _3546___mcc_h571 = _source147.dtor_range;
              bool _3547___mcc_h572 = _source147.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3548___mcc_h573 = _source147.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3549_attributes = _3548___mcc_h573;
              bool _3550_erase = _3547___mcc_h572;
              DAST._INewtypeRange _3551_range = _3546___mcc_h571;
              DAST._IType _3552_b = _3545___mcc_h570;
              {
                RAST._IExpr _out686;
                DCOMP._IOwnership _out687;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out686, out _out687, out _out688);
                r = _out686;
                resultingOwnership = _out687;
                readIdents = _out688;
              }
            }
          } else if (_source146.is_Nullable) {
            DAST._IType _3553___mcc_h578 = _source146.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source146.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3554___mcc_h580 = _source146.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source146.is_Array) {
            DAST._IType _3555___mcc_h582 = _source146.dtor_element;
            BigInteger _3556___mcc_h583 = _source146.dtor_dims;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source146.is_Seq) {
            DAST._IType _3557___mcc_h586 = _source146.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source146.is_Set) {
            DAST._IType _3558___mcc_h588 = _source146.dtor_element;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source146.is_Multiset) {
            DAST._IType _3559___mcc_h590 = _source146.dtor_element;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source146.is_Map) {
            DAST._IType _3560___mcc_h592 = _source146.dtor_key;
            DAST._IType _3561___mcc_h593 = _source146.dtor_value;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source146.is_SetBuilder) {
            DAST._IType _3562___mcc_h596 = _source146.dtor_element;
            {
              RAST._IExpr _out710;
              DCOMP._IOwnership _out711;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out710, out _out711, out _out712);
              r = _out710;
              resultingOwnership = _out711;
              readIdents = _out712;
            }
          } else if (_source146.is_MapBuilder) {
            DAST._IType _3563___mcc_h598 = _source146.dtor_key;
            DAST._IType _3564___mcc_h599 = _source146.dtor_value;
            {
              RAST._IExpr _out713;
              DCOMP._IOwnership _out714;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out715;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out713, out _out714, out _out715);
              r = _out713;
              resultingOwnership = _out714;
              readIdents = _out715;
            }
          } else if (_source146.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3565___mcc_h602 = _source146.dtor_args;
            DAST._IType _3566___mcc_h603 = _source146.dtor_result;
            {
              RAST._IExpr _out716;
              DCOMP._IOwnership _out717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out716, out _out717, out _out718);
              r = _out716;
              resultingOwnership = _out717;
              readIdents = _out718;
            }
          } else if (_source146.is_Primitive) {
            DAST._IPrimitive _3567___mcc_h606 = _source146.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out719;
              DCOMP._IOwnership _out720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out719, out _out720, out _out721);
              r = _out719;
              resultingOwnership = _out720;
              readIdents = _out721;
            }
          } else if (_source146.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3568___mcc_h608 = _source146.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out722;
              DCOMP._IOwnership _out723;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out722, out _out723, out _out724);
              r = _out722;
              resultingOwnership = _out723;
              readIdents = _out724;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3569___mcc_h610 = _source146.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out725;
              DCOMP._IOwnership _out726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out725, out _out726, out _out727);
              r = _out725;
              resultingOwnership = _out726;
              readIdents = _out727;
            }
          }
        } else if (_source128.is_Map) {
          DAST._IType _3570___mcc_h612 = _source128.dtor_key;
          DAST._IType _3571___mcc_h613 = _source128.dtor_value;
          DAST._IType _source148 = _3221___mcc_h1;
          if (_source148.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3572___mcc_h620 = _source148.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3573___mcc_h621 = _source148.dtor_typeArgs;
            DAST._IResolvedType _3574___mcc_h622 = _source148.dtor_resolved;
            DAST._IResolvedType _source149 = _3574___mcc_h622;
            if (_source149.is_Datatype) {
              DAST._IDatatypeType _3575___mcc_h626 = _source149.dtor_datatypeType;
              {
                RAST._IExpr _out728;
                DCOMP._IOwnership _out729;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out728, out _out729, out _out730);
                r = _out728;
                resultingOwnership = _out729;
                readIdents = _out730;
              }
            } else if (_source149.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3576___mcc_h628 = _source149.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3577___mcc_h629 = _source149.dtor_attributes;
              {
                RAST._IExpr _out731;
                DCOMP._IOwnership _out732;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out731, out _out732, out _out733);
                r = _out731;
                resultingOwnership = _out732;
                readIdents = _out733;
              }
            } else {
              DAST._IType _3578___mcc_h632 = _source149.dtor_baseType;
              DAST._INewtypeRange _3579___mcc_h633 = _source149.dtor_range;
              bool _3580___mcc_h634 = _source149.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3581___mcc_h635 = _source149.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3582_attributes = _3581___mcc_h635;
              bool _3583_erase = _3580___mcc_h634;
              DAST._INewtypeRange _3584_range = _3579___mcc_h633;
              DAST._IType _3585_b = _3578___mcc_h632;
              {
                RAST._IExpr _out734;
                DCOMP._IOwnership _out735;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out734, out _out735, out _out736);
                r = _out734;
                resultingOwnership = _out735;
                readIdents = _out736;
              }
            }
          } else if (_source148.is_Nullable) {
            DAST._IType _3586___mcc_h640 = _source148.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source148.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3587___mcc_h642 = _source148.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source148.is_Array) {
            DAST._IType _3588___mcc_h644 = _source148.dtor_element;
            BigInteger _3589___mcc_h645 = _source148.dtor_dims;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source148.is_Seq) {
            DAST._IType _3590___mcc_h648 = _source148.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source148.is_Set) {
            DAST._IType _3591___mcc_h650 = _source148.dtor_element;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source148.is_Multiset) {
            DAST._IType _3592___mcc_h652 = _source148.dtor_element;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source148.is_Map) {
            DAST._IType _3593___mcc_h654 = _source148.dtor_key;
            DAST._IType _3594___mcc_h655 = _source148.dtor_value;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source148.is_SetBuilder) {
            DAST._IType _3595___mcc_h658 = _source148.dtor_element;
            {
              RAST._IExpr _out758;
              DCOMP._IOwnership _out759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out760;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out758, out _out759, out _out760);
              r = _out758;
              resultingOwnership = _out759;
              readIdents = _out760;
            }
          } else if (_source148.is_MapBuilder) {
            DAST._IType _3596___mcc_h660 = _source148.dtor_key;
            DAST._IType _3597___mcc_h661 = _source148.dtor_value;
            {
              RAST._IExpr _out761;
              DCOMP._IOwnership _out762;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out763;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out761, out _out762, out _out763);
              r = _out761;
              resultingOwnership = _out762;
              readIdents = _out763;
            }
          } else if (_source148.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3598___mcc_h664 = _source148.dtor_args;
            DAST._IType _3599___mcc_h665 = _source148.dtor_result;
            {
              RAST._IExpr _out764;
              DCOMP._IOwnership _out765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out764, out _out765, out _out766);
              r = _out764;
              resultingOwnership = _out765;
              readIdents = _out766;
            }
          } else if (_source148.is_Primitive) {
            DAST._IPrimitive _3600___mcc_h668 = _source148.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out767;
              DCOMP._IOwnership _out768;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out767, out _out768, out _out769);
              r = _out767;
              resultingOwnership = _out768;
              readIdents = _out769;
            }
          } else if (_source148.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3601___mcc_h670 = _source148.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out770;
              DCOMP._IOwnership _out771;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out772;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out770, out _out771, out _out772);
              r = _out770;
              resultingOwnership = _out771;
              readIdents = _out772;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3602___mcc_h672 = _source148.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out773;
              DCOMP._IOwnership _out774;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out775;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out773, out _out774, out _out775);
              r = _out773;
              resultingOwnership = _out774;
              readIdents = _out775;
            }
          }
        } else if (_source128.is_SetBuilder) {
          DAST._IType _3603___mcc_h674 = _source128.dtor_element;
          DAST._IType _source150 = _3221___mcc_h1;
          if (_source150.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3604___mcc_h678 = _source150.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3605___mcc_h679 = _source150.dtor_typeArgs;
            DAST._IResolvedType _3606___mcc_h680 = _source150.dtor_resolved;
            DAST._IResolvedType _source151 = _3606___mcc_h680;
            if (_source151.is_Datatype) {
              DAST._IDatatypeType _3607___mcc_h684 = _source151.dtor_datatypeType;
              {
                RAST._IExpr _out776;
                DCOMP._IOwnership _out777;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out776, out _out777, out _out778);
                r = _out776;
                resultingOwnership = _out777;
                readIdents = _out778;
              }
            } else if (_source151.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3608___mcc_h686 = _source151.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3609___mcc_h687 = _source151.dtor_attributes;
              {
                RAST._IExpr _out779;
                DCOMP._IOwnership _out780;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out779, out _out780, out _out781);
                r = _out779;
                resultingOwnership = _out780;
                readIdents = _out781;
              }
            } else {
              DAST._IType _3610___mcc_h690 = _source151.dtor_baseType;
              DAST._INewtypeRange _3611___mcc_h691 = _source151.dtor_range;
              bool _3612___mcc_h692 = _source151.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3613___mcc_h693 = _source151.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3614_attributes = _3613___mcc_h693;
              bool _3615_erase = _3612___mcc_h692;
              DAST._INewtypeRange _3616_range = _3611___mcc_h691;
              DAST._IType _3617_b = _3610___mcc_h690;
              {
                RAST._IExpr _out782;
                DCOMP._IOwnership _out783;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out782, out _out783, out _out784);
                r = _out782;
                resultingOwnership = _out783;
                readIdents = _out784;
              }
            }
          } else if (_source150.is_Nullable) {
            DAST._IType _3618___mcc_h698 = _source150.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source150.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3619___mcc_h700 = _source150.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source150.is_Array) {
            DAST._IType _3620___mcc_h702 = _source150.dtor_element;
            BigInteger _3621___mcc_h703 = _source150.dtor_dims;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source150.is_Seq) {
            DAST._IType _3622___mcc_h706 = _source150.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source150.is_Set) {
            DAST._IType _3623___mcc_h708 = _source150.dtor_element;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source150.is_Multiset) {
            DAST._IType _3624___mcc_h710 = _source150.dtor_element;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source150.is_Map) {
            DAST._IType _3625___mcc_h712 = _source150.dtor_key;
            DAST._IType _3626___mcc_h713 = _source150.dtor_value;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source150.is_SetBuilder) {
            DAST._IType _3627___mcc_h716 = _source150.dtor_element;
            {
              RAST._IExpr _out806;
              DCOMP._IOwnership _out807;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out808;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out806, out _out807, out _out808);
              r = _out806;
              resultingOwnership = _out807;
              readIdents = _out808;
            }
          } else if (_source150.is_MapBuilder) {
            DAST._IType _3628___mcc_h718 = _source150.dtor_key;
            DAST._IType _3629___mcc_h719 = _source150.dtor_value;
            {
              RAST._IExpr _out809;
              DCOMP._IOwnership _out810;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out811;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out809, out _out810, out _out811);
              r = _out809;
              resultingOwnership = _out810;
              readIdents = _out811;
            }
          } else if (_source150.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3630___mcc_h722 = _source150.dtor_args;
            DAST._IType _3631___mcc_h723 = _source150.dtor_result;
            {
              RAST._IExpr _out812;
              DCOMP._IOwnership _out813;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out812, out _out813, out _out814);
              r = _out812;
              resultingOwnership = _out813;
              readIdents = _out814;
            }
          } else if (_source150.is_Primitive) {
            DAST._IPrimitive _3632___mcc_h726 = _source150.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out815;
              DCOMP._IOwnership _out816;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out815, out _out816, out _out817);
              r = _out815;
              resultingOwnership = _out816;
              readIdents = _out817;
            }
          } else if (_source150.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3633___mcc_h728 = _source150.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out818;
              DCOMP._IOwnership _out819;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out820;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out818, out _out819, out _out820);
              r = _out818;
              resultingOwnership = _out819;
              readIdents = _out820;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3634___mcc_h730 = _source150.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out821;
              DCOMP._IOwnership _out822;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out821, out _out822, out _out823);
              r = _out821;
              resultingOwnership = _out822;
              readIdents = _out823;
            }
          }
        } else if (_source128.is_MapBuilder) {
          DAST._IType _3635___mcc_h732 = _source128.dtor_key;
          DAST._IType _3636___mcc_h733 = _source128.dtor_value;
          DAST._IType _source152 = _3221___mcc_h1;
          if (_source152.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3637___mcc_h740 = _source152.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3638___mcc_h741 = _source152.dtor_typeArgs;
            DAST._IResolvedType _3639___mcc_h742 = _source152.dtor_resolved;
            DAST._IResolvedType _source153 = _3639___mcc_h742;
            if (_source153.is_Datatype) {
              DAST._IDatatypeType _3640___mcc_h746 = _source153.dtor_datatypeType;
              {
                RAST._IExpr _out824;
                DCOMP._IOwnership _out825;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out824, out _out825, out _out826);
                r = _out824;
                resultingOwnership = _out825;
                readIdents = _out826;
              }
            } else if (_source153.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3641___mcc_h748 = _source153.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3642___mcc_h749 = _source153.dtor_attributes;
              {
                RAST._IExpr _out827;
                DCOMP._IOwnership _out828;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out829;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out827, out _out828, out _out829);
                r = _out827;
                resultingOwnership = _out828;
                readIdents = _out829;
              }
            } else {
              DAST._IType _3643___mcc_h752 = _source153.dtor_baseType;
              DAST._INewtypeRange _3644___mcc_h753 = _source153.dtor_range;
              bool _3645___mcc_h754 = _source153.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3646___mcc_h755 = _source153.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3647_attributes = _3646___mcc_h755;
              bool _3648_erase = _3645___mcc_h754;
              DAST._INewtypeRange _3649_range = _3644___mcc_h753;
              DAST._IType _3650_b = _3643___mcc_h752;
              {
                RAST._IExpr _out830;
                DCOMP._IOwnership _out831;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out830, out _out831, out _out832);
                r = _out830;
                resultingOwnership = _out831;
                readIdents = _out832;
              }
            }
          } else if (_source152.is_Nullable) {
            DAST._IType _3651___mcc_h760 = _source152.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source152.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3652___mcc_h762 = _source152.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source152.is_Array) {
            DAST._IType _3653___mcc_h764 = _source152.dtor_element;
            BigInteger _3654___mcc_h765 = _source152.dtor_dims;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source152.is_Seq) {
            DAST._IType _3655___mcc_h768 = _source152.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source152.is_Set) {
            DAST._IType _3656___mcc_h770 = _source152.dtor_element;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source152.is_Multiset) {
            DAST._IType _3657___mcc_h772 = _source152.dtor_element;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source152.is_Map) {
            DAST._IType _3658___mcc_h774 = _source152.dtor_key;
            DAST._IType _3659___mcc_h775 = _source152.dtor_value;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source152.is_SetBuilder) {
            DAST._IType _3660___mcc_h778 = _source152.dtor_element;
            {
              RAST._IExpr _out854;
              DCOMP._IOwnership _out855;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out856;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out854, out _out855, out _out856);
              r = _out854;
              resultingOwnership = _out855;
              readIdents = _out856;
            }
          } else if (_source152.is_MapBuilder) {
            DAST._IType _3661___mcc_h780 = _source152.dtor_key;
            DAST._IType _3662___mcc_h781 = _source152.dtor_value;
            {
              RAST._IExpr _out857;
              DCOMP._IOwnership _out858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out857, out _out858, out _out859);
              r = _out857;
              resultingOwnership = _out858;
              readIdents = _out859;
            }
          } else if (_source152.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3663___mcc_h784 = _source152.dtor_args;
            DAST._IType _3664___mcc_h785 = _source152.dtor_result;
            {
              RAST._IExpr _out860;
              DCOMP._IOwnership _out861;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out860, out _out861, out _out862);
              r = _out860;
              resultingOwnership = _out861;
              readIdents = _out862;
            }
          } else if (_source152.is_Primitive) {
            DAST._IPrimitive _3665___mcc_h788 = _source152.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out863;
              DCOMP._IOwnership _out864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out865;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out863, out _out864, out _out865);
              r = _out863;
              resultingOwnership = _out864;
              readIdents = _out865;
            }
          } else if (_source152.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3666___mcc_h790 = _source152.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out866;
              DCOMP._IOwnership _out867;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out868;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out866, out _out867, out _out868);
              r = _out866;
              resultingOwnership = _out867;
              readIdents = _out868;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3667___mcc_h792 = _source152.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out869;
              DCOMP._IOwnership _out870;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out869, out _out870, out _out871);
              r = _out869;
              resultingOwnership = _out870;
              readIdents = _out871;
            }
          }
        } else if (_source128.is_Arrow) {
          Dafny.ISequence<DAST._IType> _3668___mcc_h794 = _source128.dtor_args;
          DAST._IType _3669___mcc_h795 = _source128.dtor_result;
          DAST._IType _source154 = _3221___mcc_h1;
          if (_source154.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3670___mcc_h802 = _source154.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3671___mcc_h803 = _source154.dtor_typeArgs;
            DAST._IResolvedType _3672___mcc_h804 = _source154.dtor_resolved;
            DAST._IResolvedType _source155 = _3672___mcc_h804;
            if (_source155.is_Datatype) {
              DAST._IDatatypeType _3673___mcc_h808 = _source155.dtor_datatypeType;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source155.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3674___mcc_h810 = _source155.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3675___mcc_h811 = _source155.dtor_attributes;
              {
                RAST._IExpr _out875;
                DCOMP._IOwnership _out876;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out875, out _out876, out _out877);
                r = _out875;
                resultingOwnership = _out876;
                readIdents = _out877;
              }
            } else {
              DAST._IType _3676___mcc_h814 = _source155.dtor_baseType;
              DAST._INewtypeRange _3677___mcc_h815 = _source155.dtor_range;
              bool _3678___mcc_h816 = _source155.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3679___mcc_h817 = _source155.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3680_attributes = _3679___mcc_h817;
              bool _3681_erase = _3678___mcc_h816;
              DAST._INewtypeRange _3682_range = _3677___mcc_h815;
              DAST._IType _3683_b = _3676___mcc_h814;
              {
                RAST._IExpr _out878;
                DCOMP._IOwnership _out879;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out880;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out878, out _out879, out _out880);
                r = _out878;
                resultingOwnership = _out879;
                readIdents = _out880;
              }
            }
          } else if (_source154.is_Nullable) {
            DAST._IType _3684___mcc_h822 = _source154.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out881;
              DCOMP._IOwnership _out882;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out881, out _out882, out _out883);
              r = _out881;
              resultingOwnership = _out882;
              readIdents = _out883;
            }
          } else if (_source154.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3685___mcc_h824 = _source154.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out884;
              DCOMP._IOwnership _out885;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out884, out _out885, out _out886);
              r = _out884;
              resultingOwnership = _out885;
              readIdents = _out886;
            }
          } else if (_source154.is_Array) {
            DAST._IType _3686___mcc_h826 = _source154.dtor_element;
            BigInteger _3687___mcc_h827 = _source154.dtor_dims;
            {
              RAST._IExpr _out887;
              DCOMP._IOwnership _out888;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out887, out _out888, out _out889);
              r = _out887;
              resultingOwnership = _out888;
              readIdents = _out889;
            }
          } else if (_source154.is_Seq) {
            DAST._IType _3688___mcc_h830 = _source154.dtor_element;
            {
              RAST._IExpr _out890;
              DCOMP._IOwnership _out891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out890, out _out891, out _out892);
              r = _out890;
              resultingOwnership = _out891;
              readIdents = _out892;
            }
          } else if (_source154.is_Set) {
            DAST._IType _3689___mcc_h832 = _source154.dtor_element;
            {
              RAST._IExpr _out893;
              DCOMP._IOwnership _out894;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out893, out _out894, out _out895);
              r = _out893;
              resultingOwnership = _out894;
              readIdents = _out895;
            }
          } else if (_source154.is_Multiset) {
            DAST._IType _3690___mcc_h834 = _source154.dtor_element;
            {
              RAST._IExpr _out896;
              DCOMP._IOwnership _out897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out896, out _out897, out _out898);
              r = _out896;
              resultingOwnership = _out897;
              readIdents = _out898;
            }
          } else if (_source154.is_Map) {
            DAST._IType _3691___mcc_h836 = _source154.dtor_key;
            DAST._IType _3692___mcc_h837 = _source154.dtor_value;
            {
              RAST._IExpr _out899;
              DCOMP._IOwnership _out900;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out899, out _out900, out _out901);
              r = _out899;
              resultingOwnership = _out900;
              readIdents = _out901;
            }
          } else if (_source154.is_SetBuilder) {
            DAST._IType _3693___mcc_h840 = _source154.dtor_element;
            {
              RAST._IExpr _out902;
              DCOMP._IOwnership _out903;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out902, out _out903, out _out904);
              r = _out902;
              resultingOwnership = _out903;
              readIdents = _out904;
            }
          } else if (_source154.is_MapBuilder) {
            DAST._IType _3694___mcc_h842 = _source154.dtor_key;
            DAST._IType _3695___mcc_h843 = _source154.dtor_value;
            {
              RAST._IExpr _out905;
              DCOMP._IOwnership _out906;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out905, out _out906, out _out907);
              r = _out905;
              resultingOwnership = _out906;
              readIdents = _out907;
            }
          } else if (_source154.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3696___mcc_h846 = _source154.dtor_args;
            DAST._IType _3697___mcc_h847 = _source154.dtor_result;
            {
              RAST._IExpr _out908;
              DCOMP._IOwnership _out909;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out910;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out908, out _out909, out _out910);
              r = _out908;
              resultingOwnership = _out909;
              readIdents = _out910;
            }
          } else if (_source154.is_Primitive) {
            DAST._IPrimitive _3698___mcc_h850 = _source154.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out911;
              DCOMP._IOwnership _out912;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out913;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out911, out _out912, out _out913);
              r = _out911;
              resultingOwnership = _out912;
              readIdents = _out913;
            }
          } else if (_source154.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3699___mcc_h852 = _source154.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out914;
              DCOMP._IOwnership _out915;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out914, out _out915, out _out916);
              r = _out914;
              resultingOwnership = _out915;
              readIdents = _out916;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3700___mcc_h854 = _source154.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out917;
              DCOMP._IOwnership _out918;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out917, out _out918, out _out919);
              r = _out917;
              resultingOwnership = _out918;
              readIdents = _out919;
            }
          }
        } else if (_source128.is_Primitive) {
          DAST._IPrimitive _3701___mcc_h856 = _source128.dtor_Primitive_i_a0;
          DAST._IPrimitive _source156 = _3701___mcc_h856;
          if (_source156.is_Int) {
            DAST._IType _source157 = _3221___mcc_h1;
            if (_source157.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3702___mcc_h860 = _source157.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3703___mcc_h861 = _source157.dtor_typeArgs;
              DAST._IResolvedType _3704___mcc_h862 = _source157.dtor_resolved;
              DAST._IResolvedType _source158 = _3704___mcc_h862;
              if (_source158.is_Datatype) {
                DAST._IDatatypeType _3705___mcc_h866 = _source158.dtor_datatypeType;
                {
                  RAST._IExpr _out920;
                  DCOMP._IOwnership _out921;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out920, out _out921, out _out922);
                  r = _out920;
                  resultingOwnership = _out921;
                  readIdents = _out922;
                }
              } else if (_source158.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3706___mcc_h868 = _source158.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3707___mcc_h869 = _source158.dtor_attributes;
                {
                  RAST._IExpr _out923;
                  DCOMP._IOwnership _out924;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out925;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out923, out _out924, out _out925);
                  r = _out923;
                  resultingOwnership = _out924;
                  readIdents = _out925;
                }
              } else {
                DAST._IType _3708___mcc_h872 = _source158.dtor_baseType;
                DAST._INewtypeRange _3709___mcc_h873 = _source158.dtor_range;
                bool _3710___mcc_h874 = _source158.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3711___mcc_h875 = _source158.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3712_attributes = _3711___mcc_h875;
                bool _3713_erase = _3710___mcc_h874;
                DAST._INewtypeRange _3714_range = _3709___mcc_h873;
                DAST._IType _3715_b = _3708___mcc_h872;
                {
                  RAST._IExpr _out926;
                  DCOMP._IOwnership _out927;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out928;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out926, out _out927, out _out928);
                  r = _out926;
                  resultingOwnership = _out927;
                  readIdents = _out928;
                }
              }
            } else if (_source157.is_Nullable) {
              DAST._IType _3716___mcc_h880 = _source157.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out929;
                DCOMP._IOwnership _out930;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out929, out _out930, out _out931);
                r = _out929;
                resultingOwnership = _out930;
                readIdents = _out931;
              }
            } else if (_source157.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3717___mcc_h882 = _source157.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out932;
                DCOMP._IOwnership _out933;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out934;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out932, out _out933, out _out934);
                r = _out932;
                resultingOwnership = _out933;
                readIdents = _out934;
              }
            } else if (_source157.is_Array) {
              DAST._IType _3718___mcc_h884 = _source157.dtor_element;
              BigInteger _3719___mcc_h885 = _source157.dtor_dims;
              {
                RAST._IExpr _out935;
                DCOMP._IOwnership _out936;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out937;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out935, out _out936, out _out937);
                r = _out935;
                resultingOwnership = _out936;
                readIdents = _out937;
              }
            } else if (_source157.is_Seq) {
              DAST._IType _3720___mcc_h888 = _source157.dtor_element;
              {
                RAST._IExpr _out938;
                DCOMP._IOwnership _out939;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out940;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out938, out _out939, out _out940);
                r = _out938;
                resultingOwnership = _out939;
                readIdents = _out940;
              }
            } else if (_source157.is_Set) {
              DAST._IType _3721___mcc_h890 = _source157.dtor_element;
              {
                RAST._IExpr _out941;
                DCOMP._IOwnership _out942;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out943;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out941, out _out942, out _out943);
                r = _out941;
                resultingOwnership = _out942;
                readIdents = _out943;
              }
            } else if (_source157.is_Multiset) {
              DAST._IType _3722___mcc_h892 = _source157.dtor_element;
              {
                RAST._IExpr _out944;
                DCOMP._IOwnership _out945;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out946;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out944, out _out945, out _out946);
                r = _out944;
                resultingOwnership = _out945;
                readIdents = _out946;
              }
            } else if (_source157.is_Map) {
              DAST._IType _3723___mcc_h894 = _source157.dtor_key;
              DAST._IType _3724___mcc_h895 = _source157.dtor_value;
              {
                RAST._IExpr _out947;
                DCOMP._IOwnership _out948;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out947, out _out948, out _out949);
                r = _out947;
                resultingOwnership = _out948;
                readIdents = _out949;
              }
            } else if (_source157.is_SetBuilder) {
              DAST._IType _3725___mcc_h898 = _source157.dtor_element;
              {
                RAST._IExpr _out950;
                DCOMP._IOwnership _out951;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out952;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out950, out _out951, out _out952);
                r = _out950;
                resultingOwnership = _out951;
                readIdents = _out952;
              }
            } else if (_source157.is_MapBuilder) {
              DAST._IType _3726___mcc_h900 = _source157.dtor_key;
              DAST._IType _3727___mcc_h901 = _source157.dtor_value;
              {
                RAST._IExpr _out953;
                DCOMP._IOwnership _out954;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out955;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out953, out _out954, out _out955);
                r = _out953;
                resultingOwnership = _out954;
                readIdents = _out955;
              }
            } else if (_source157.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3728___mcc_h904 = _source157.dtor_args;
              DAST._IType _3729___mcc_h905 = _source157.dtor_result;
              {
                RAST._IExpr _out956;
                DCOMP._IOwnership _out957;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out958;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out956, out _out957, out _out958);
                r = _out956;
                resultingOwnership = _out957;
                readIdents = _out958;
              }
            } else if (_source157.is_Primitive) {
              DAST._IPrimitive _3730___mcc_h908 = _source157.dtor_Primitive_i_a0;
              DAST._IPrimitive _source159 = _3730___mcc_h908;
              if (_source159.is_Int) {
                {
                  RAST._IExpr _out959;
                  DCOMP._IOwnership _out960;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out961;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out959, out _out960, out _out961);
                  r = _out959;
                  resultingOwnership = _out960;
                  readIdents = _out961;
                }
              } else if (_source159.is_Real) {
                {
                  RAST._IExpr _3731_recursiveGen;
                  DCOMP._IOwnership _3732___v98;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3733_recIdents;
                  RAST._IExpr _out962;
                  DCOMP._IOwnership _out963;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out964;
                  (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out962, out _out963, out _out964);
                  _3731_recursiveGen = _out962;
                  _3732___v98 = _out963;
                  _3733_recIdents = _out964;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_3731_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out965;
                  DCOMP._IOwnership _out966;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out965, out _out966);
                  r = _out965;
                  resultingOwnership = _out966;
                  readIdents = _3733_recIdents;
                }
              } else if (_source159.is_String) {
                {
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out967, out _out968, out _out969);
                  r = _out967;
                  resultingOwnership = _out968;
                  readIdents = _out969;
                }
              } else if (_source159.is_Bool) {
                {
                  RAST._IExpr _out970;
                  DCOMP._IOwnership _out971;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out972;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out970, out _out971, out _out972);
                  r = _out970;
                  resultingOwnership = _out971;
                  readIdents = _out972;
                }
              } else {
                {
                  RAST._IType _3734_rhsType;
                  RAST._IType _out973;
                  _out973 = (this).GenType(_3216_toTpe, true, false);
                  _3734_rhsType = _out973;
                  RAST._IExpr _3735_recursiveGen;
                  DCOMP._IOwnership _3736___v104;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3737_recIdents;
                  RAST._IExpr _out974;
                  DCOMP._IOwnership _out975;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out976;
                  (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out974, out _out975, out _out976);
                  _3735_recursiveGen = _out974;
                  _3736___v104 = _out975;
                  _3737_recIdents = _out976;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3735_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out977;
                  DCOMP._IOwnership _out978;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out977, out _out978);
                  r = _out977;
                  resultingOwnership = _out978;
                  readIdents = _3737_recIdents;
                }
              }
            } else if (_source157.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3738___mcc_h910 = _source157.dtor_Passthrough_i_a0;
              {
                RAST._IType _3739_rhsType;
                RAST._IType _out979;
                _out979 = (this).GenType(_3216_toTpe, true, false);
                _3739_rhsType = _out979;
                RAST._IExpr _3740_recursiveGen;
                DCOMP._IOwnership _3741___v101;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3742_recIdents;
                RAST._IExpr _out980;
                DCOMP._IOwnership _out981;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out980, out _out981, out _out982);
                _3740_recursiveGen = _out980;
                _3741___v101 = _out981;
                _3742_recIdents = _out982;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3739_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3740_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out983;
                DCOMP._IOwnership _out984;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out983, out _out984);
                r = _out983;
                resultingOwnership = _out984;
                readIdents = _3742_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3743___mcc_h912 = _source157.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out985;
                DCOMP._IOwnership _out986;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out987;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out985, out _out986, out _out987);
                r = _out985;
                resultingOwnership = _out986;
                readIdents = _out987;
              }
            }
          } else if (_source156.is_Real) {
            DAST._IType _source160 = _3221___mcc_h1;
            if (_source160.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3744___mcc_h914 = _source160.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3745___mcc_h915 = _source160.dtor_typeArgs;
              DAST._IResolvedType _3746___mcc_h916 = _source160.dtor_resolved;
              DAST._IResolvedType _source161 = _3746___mcc_h916;
              if (_source161.is_Datatype) {
                DAST._IDatatypeType _3747___mcc_h920 = _source161.dtor_datatypeType;
                {
                  RAST._IExpr _out988;
                  DCOMP._IOwnership _out989;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out988, out _out989, out _out990);
                  r = _out988;
                  resultingOwnership = _out989;
                  readIdents = _out990;
                }
              } else if (_source161.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3748___mcc_h922 = _source161.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3749___mcc_h923 = _source161.dtor_attributes;
                {
                  RAST._IExpr _out991;
                  DCOMP._IOwnership _out992;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out993;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out991, out _out992, out _out993);
                  r = _out991;
                  resultingOwnership = _out992;
                  readIdents = _out993;
                }
              } else {
                DAST._IType _3750___mcc_h926 = _source161.dtor_baseType;
                DAST._INewtypeRange _3751___mcc_h927 = _source161.dtor_range;
                bool _3752___mcc_h928 = _source161.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3753___mcc_h929 = _source161.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3754_attributes = _3753___mcc_h929;
                bool _3755_erase = _3752___mcc_h928;
                DAST._INewtypeRange _3756_range = _3751___mcc_h927;
                DAST._IType _3757_b = _3750___mcc_h926;
                {
                  RAST._IExpr _out994;
                  DCOMP._IOwnership _out995;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out996;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out994, out _out995, out _out996);
                  r = _out994;
                  resultingOwnership = _out995;
                  readIdents = _out996;
                }
              }
            } else if (_source160.is_Nullable) {
              DAST._IType _3758___mcc_h934 = _source160.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out997;
                DCOMP._IOwnership _out998;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out999;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out997, out _out998, out _out999);
                r = _out997;
                resultingOwnership = _out998;
                readIdents = _out999;
              }
            } else if (_source160.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3759___mcc_h936 = _source160.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1000;
                DCOMP._IOwnership _out1001;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1000, out _out1001, out _out1002);
                r = _out1000;
                resultingOwnership = _out1001;
                readIdents = _out1002;
              }
            } else if (_source160.is_Array) {
              DAST._IType _3760___mcc_h938 = _source160.dtor_element;
              BigInteger _3761___mcc_h939 = _source160.dtor_dims;
              {
                RAST._IExpr _out1003;
                DCOMP._IOwnership _out1004;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1005;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1003, out _out1004, out _out1005);
                r = _out1003;
                resultingOwnership = _out1004;
                readIdents = _out1005;
              }
            } else if (_source160.is_Seq) {
              DAST._IType _3762___mcc_h942 = _source160.dtor_element;
              {
                RAST._IExpr _out1006;
                DCOMP._IOwnership _out1007;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1008;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1006, out _out1007, out _out1008);
                r = _out1006;
                resultingOwnership = _out1007;
                readIdents = _out1008;
              }
            } else if (_source160.is_Set) {
              DAST._IType _3763___mcc_h944 = _source160.dtor_element;
              {
                RAST._IExpr _out1009;
                DCOMP._IOwnership _out1010;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1011;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1009, out _out1010, out _out1011);
                r = _out1009;
                resultingOwnership = _out1010;
                readIdents = _out1011;
              }
            } else if (_source160.is_Multiset) {
              DAST._IType _3764___mcc_h946 = _source160.dtor_element;
              {
                RAST._IExpr _out1012;
                DCOMP._IOwnership _out1013;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1012, out _out1013, out _out1014);
                r = _out1012;
                resultingOwnership = _out1013;
                readIdents = _out1014;
              }
            } else if (_source160.is_Map) {
              DAST._IType _3765___mcc_h948 = _source160.dtor_key;
              DAST._IType _3766___mcc_h949 = _source160.dtor_value;
              {
                RAST._IExpr _out1015;
                DCOMP._IOwnership _out1016;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1017;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1015, out _out1016, out _out1017);
                r = _out1015;
                resultingOwnership = _out1016;
                readIdents = _out1017;
              }
            } else if (_source160.is_SetBuilder) {
              DAST._IType _3767___mcc_h952 = _source160.dtor_element;
              {
                RAST._IExpr _out1018;
                DCOMP._IOwnership _out1019;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1020;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1018, out _out1019, out _out1020);
                r = _out1018;
                resultingOwnership = _out1019;
                readIdents = _out1020;
              }
            } else if (_source160.is_MapBuilder) {
              DAST._IType _3768___mcc_h954 = _source160.dtor_key;
              DAST._IType _3769___mcc_h955 = _source160.dtor_value;
              {
                RAST._IExpr _out1021;
                DCOMP._IOwnership _out1022;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1023;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1021, out _out1022, out _out1023);
                r = _out1021;
                resultingOwnership = _out1022;
                readIdents = _out1023;
              }
            } else if (_source160.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3770___mcc_h958 = _source160.dtor_args;
              DAST._IType _3771___mcc_h959 = _source160.dtor_result;
              {
                RAST._IExpr _out1024;
                DCOMP._IOwnership _out1025;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1024, out _out1025, out _out1026);
                r = _out1024;
                resultingOwnership = _out1025;
                readIdents = _out1026;
              }
            } else if (_source160.is_Primitive) {
              DAST._IPrimitive _3772___mcc_h962 = _source160.dtor_Primitive_i_a0;
              DAST._IPrimitive _source162 = _3772___mcc_h962;
              if (_source162.is_Int) {
                {
                  RAST._IExpr _3773_recursiveGen;
                  DCOMP._IOwnership _3774___v99;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3775_recIdents;
                  RAST._IExpr _out1027;
                  DCOMP._IOwnership _out1028;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1029;
                  (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1027, out _out1028, out _out1029);
                  _3773_recursiveGen = _out1027;
                  _3774___v99 = _out1028;
                  _3775_recIdents = _out1029;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3773_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out1030;
                  DCOMP._IOwnership _out1031;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1030, out _out1031);
                  r = _out1030;
                  resultingOwnership = _out1031;
                  readIdents = _3775_recIdents;
                }
              } else if (_source162.is_Real) {
                {
                  RAST._IExpr _out1032;
                  DCOMP._IOwnership _out1033;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1032, out _out1033, out _out1034);
                  r = _out1032;
                  resultingOwnership = _out1033;
                  readIdents = _out1034;
                }
              } else if (_source162.is_String) {
                {
                  RAST._IExpr _out1035;
                  DCOMP._IOwnership _out1036;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1037;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1035, out _out1036, out _out1037);
                  r = _out1035;
                  resultingOwnership = _out1036;
                  readIdents = _out1037;
                }
              } else if (_source162.is_Bool) {
                {
                  RAST._IExpr _out1038;
                  DCOMP._IOwnership _out1039;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1038, out _out1039, out _out1040);
                  r = _out1038;
                  resultingOwnership = _out1039;
                  readIdents = _out1040;
                }
              } else {
                {
                  RAST._IExpr _out1041;
                  DCOMP._IOwnership _out1042;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1041, out _out1042, out _out1043);
                  r = _out1041;
                  resultingOwnership = _out1042;
                  readIdents = _out1043;
                }
              }
            } else if (_source160.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3776___mcc_h964 = _source160.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1044;
                DCOMP._IOwnership _out1045;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1046;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1044, out _out1045, out _out1046);
                r = _out1044;
                resultingOwnership = _out1045;
                readIdents = _out1046;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3777___mcc_h966 = _source160.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1047;
                DCOMP._IOwnership _out1048;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1049;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1047, out _out1048, out _out1049);
                r = _out1047;
                resultingOwnership = _out1048;
                readIdents = _out1049;
              }
            }
          } else if (_source156.is_String) {
            DAST._IType _source163 = _3221___mcc_h1;
            if (_source163.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3778___mcc_h968 = _source163.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3779___mcc_h969 = _source163.dtor_typeArgs;
              DAST._IResolvedType _3780___mcc_h970 = _source163.dtor_resolved;
              DAST._IResolvedType _source164 = _3780___mcc_h970;
              if (_source164.is_Datatype) {
                DAST._IDatatypeType _3781___mcc_h974 = _source164.dtor_datatypeType;
                {
                  RAST._IExpr _out1050;
                  DCOMP._IOwnership _out1051;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1050, out _out1051, out _out1052);
                  r = _out1050;
                  resultingOwnership = _out1051;
                  readIdents = _out1052;
                }
              } else if (_source164.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3782___mcc_h976 = _source164.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3783___mcc_h977 = _source164.dtor_attributes;
                {
                  RAST._IExpr _out1053;
                  DCOMP._IOwnership _out1054;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1053, out _out1054, out _out1055);
                  r = _out1053;
                  resultingOwnership = _out1054;
                  readIdents = _out1055;
                }
              } else {
                DAST._IType _3784___mcc_h980 = _source164.dtor_baseType;
                DAST._INewtypeRange _3785___mcc_h981 = _source164.dtor_range;
                bool _3786___mcc_h982 = _source164.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3787___mcc_h983 = _source164.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3788_attributes = _3787___mcc_h983;
                bool _3789_erase = _3786___mcc_h982;
                DAST._INewtypeRange _3790_range = _3785___mcc_h981;
                DAST._IType _3791_b = _3784___mcc_h980;
                {
                  RAST._IExpr _out1056;
                  DCOMP._IOwnership _out1057;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1056, out _out1057, out _out1058);
                  r = _out1056;
                  resultingOwnership = _out1057;
                  readIdents = _out1058;
                }
              }
            } else if (_source163.is_Nullable) {
              DAST._IType _3792___mcc_h988 = _source163.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source163.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3793___mcc_h990 = _source163.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source163.is_Array) {
              DAST._IType _3794___mcc_h992 = _source163.dtor_element;
              BigInteger _3795___mcc_h993 = _source163.dtor_dims;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source163.is_Seq) {
              DAST._IType _3796___mcc_h996 = _source163.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source163.is_Set) {
              DAST._IType _3797___mcc_h998 = _source163.dtor_element;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source163.is_Multiset) {
              DAST._IType _3798___mcc_h1000 = _source163.dtor_element;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source163.is_Map) {
              DAST._IType _3799___mcc_h1002 = _source163.dtor_key;
              DAST._IType _3800___mcc_h1003 = _source163.dtor_value;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source163.is_SetBuilder) {
              DAST._IType _3801___mcc_h1006 = _source163.dtor_element;
              {
                RAST._IExpr _out1080;
                DCOMP._IOwnership _out1081;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1082;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1080, out _out1081, out _out1082);
                r = _out1080;
                resultingOwnership = _out1081;
                readIdents = _out1082;
              }
            } else if (_source163.is_MapBuilder) {
              DAST._IType _3802___mcc_h1008 = _source163.dtor_key;
              DAST._IType _3803___mcc_h1009 = _source163.dtor_value;
              {
                RAST._IExpr _out1083;
                DCOMP._IOwnership _out1084;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1085;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1083, out _out1084, out _out1085);
                r = _out1083;
                resultingOwnership = _out1084;
                readIdents = _out1085;
              }
            } else if (_source163.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3804___mcc_h1012 = _source163.dtor_args;
              DAST._IType _3805___mcc_h1013 = _source163.dtor_result;
              {
                RAST._IExpr _out1086;
                DCOMP._IOwnership _out1087;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1086, out _out1087, out _out1088);
                r = _out1086;
                resultingOwnership = _out1087;
                readIdents = _out1088;
              }
            } else if (_source163.is_Primitive) {
              DAST._IPrimitive _3806___mcc_h1016 = _source163.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1089;
                DCOMP._IOwnership _out1090;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1089, out _out1090, out _out1091);
                r = _out1089;
                resultingOwnership = _out1090;
                readIdents = _out1091;
              }
            } else if (_source163.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3807___mcc_h1018 = _source163.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1092;
                DCOMP._IOwnership _out1093;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1094;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1092, out _out1093, out _out1094);
                r = _out1092;
                resultingOwnership = _out1093;
                readIdents = _out1094;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3808___mcc_h1020 = _source163.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1095;
                DCOMP._IOwnership _out1096;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1095, out _out1096, out _out1097);
                r = _out1095;
                resultingOwnership = _out1096;
                readIdents = _out1097;
              }
            }
          } else if (_source156.is_Bool) {
            DAST._IType _source165 = _3221___mcc_h1;
            if (_source165.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3809___mcc_h1022 = _source165.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3810___mcc_h1023 = _source165.dtor_typeArgs;
              DAST._IResolvedType _3811___mcc_h1024 = _source165.dtor_resolved;
              DAST._IResolvedType _source166 = _3811___mcc_h1024;
              if (_source166.is_Datatype) {
                DAST._IDatatypeType _3812___mcc_h1028 = _source166.dtor_datatypeType;
                {
                  RAST._IExpr _out1098;
                  DCOMP._IOwnership _out1099;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1098, out _out1099, out _out1100);
                  r = _out1098;
                  resultingOwnership = _out1099;
                  readIdents = _out1100;
                }
              } else if (_source166.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3813___mcc_h1030 = _source166.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3814___mcc_h1031 = _source166.dtor_attributes;
                {
                  RAST._IExpr _out1101;
                  DCOMP._IOwnership _out1102;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1101, out _out1102, out _out1103);
                  r = _out1101;
                  resultingOwnership = _out1102;
                  readIdents = _out1103;
                }
              } else {
                DAST._IType _3815___mcc_h1034 = _source166.dtor_baseType;
                DAST._INewtypeRange _3816___mcc_h1035 = _source166.dtor_range;
                bool _3817___mcc_h1036 = _source166.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3818___mcc_h1037 = _source166.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3819_attributes = _3818___mcc_h1037;
                bool _3820_erase = _3817___mcc_h1036;
                DAST._INewtypeRange _3821_range = _3816___mcc_h1035;
                DAST._IType _3822_b = _3815___mcc_h1034;
                {
                  RAST._IExpr _out1104;
                  DCOMP._IOwnership _out1105;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1106;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1104, out _out1105, out _out1106);
                  r = _out1104;
                  resultingOwnership = _out1105;
                  readIdents = _out1106;
                }
              }
            } else if (_source165.is_Nullable) {
              DAST._IType _3823___mcc_h1042 = _source165.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source165.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3824___mcc_h1044 = _source165.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source165.is_Array) {
              DAST._IType _3825___mcc_h1046 = _source165.dtor_element;
              BigInteger _3826___mcc_h1047 = _source165.dtor_dims;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source165.is_Seq) {
              DAST._IType _3827___mcc_h1050 = _source165.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source165.is_Set) {
              DAST._IType _3828___mcc_h1052 = _source165.dtor_element;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source165.is_Multiset) {
              DAST._IType _3829___mcc_h1054 = _source165.dtor_element;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source165.is_Map) {
              DAST._IType _3830___mcc_h1056 = _source165.dtor_key;
              DAST._IType _3831___mcc_h1057 = _source165.dtor_value;
              {
                RAST._IExpr _out1125;
                DCOMP._IOwnership _out1126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1127;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1125, out _out1126, out _out1127);
                r = _out1125;
                resultingOwnership = _out1126;
                readIdents = _out1127;
              }
            } else if (_source165.is_SetBuilder) {
              DAST._IType _3832___mcc_h1060 = _source165.dtor_element;
              {
                RAST._IExpr _out1128;
                DCOMP._IOwnership _out1129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1130;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1128, out _out1129, out _out1130);
                r = _out1128;
                resultingOwnership = _out1129;
                readIdents = _out1130;
              }
            } else if (_source165.is_MapBuilder) {
              DAST._IType _3833___mcc_h1062 = _source165.dtor_key;
              DAST._IType _3834___mcc_h1063 = _source165.dtor_value;
              {
                RAST._IExpr _out1131;
                DCOMP._IOwnership _out1132;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1131, out _out1132, out _out1133);
                r = _out1131;
                resultingOwnership = _out1132;
                readIdents = _out1133;
              }
            } else if (_source165.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3835___mcc_h1066 = _source165.dtor_args;
              DAST._IType _3836___mcc_h1067 = _source165.dtor_result;
              {
                RAST._IExpr _out1134;
                DCOMP._IOwnership _out1135;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1134, out _out1135, out _out1136);
                r = _out1134;
                resultingOwnership = _out1135;
                readIdents = _out1136;
              }
            } else if (_source165.is_Primitive) {
              DAST._IPrimitive _3837___mcc_h1070 = _source165.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1137;
                DCOMP._IOwnership _out1138;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1139;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1137, out _out1138, out _out1139);
                r = _out1137;
                resultingOwnership = _out1138;
                readIdents = _out1139;
              }
            } else if (_source165.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3838___mcc_h1072 = _source165.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1140;
                DCOMP._IOwnership _out1141;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1142;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1140, out _out1141, out _out1142);
                r = _out1140;
                resultingOwnership = _out1141;
                readIdents = _out1142;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3839___mcc_h1074 = _source165.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1143;
                DCOMP._IOwnership _out1144;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1145;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1143, out _out1144, out _out1145);
                r = _out1143;
                resultingOwnership = _out1144;
                readIdents = _out1145;
              }
            }
          } else {
            DAST._IType _source167 = _3221___mcc_h1;
            if (_source167.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3840___mcc_h1076 = _source167.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3841___mcc_h1077 = _source167.dtor_typeArgs;
              DAST._IResolvedType _3842___mcc_h1078 = _source167.dtor_resolved;
              DAST._IResolvedType _source168 = _3842___mcc_h1078;
              if (_source168.is_Datatype) {
                DAST._IDatatypeType _3843___mcc_h1082 = _source168.dtor_datatypeType;
                {
                  RAST._IExpr _out1146;
                  DCOMP._IOwnership _out1147;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1146, out _out1147, out _out1148);
                  r = _out1146;
                  resultingOwnership = _out1147;
                  readIdents = _out1148;
                }
              } else if (_source168.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3844___mcc_h1084 = _source168.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3845___mcc_h1085 = _source168.dtor_attributes;
                {
                  RAST._IExpr _out1149;
                  DCOMP._IOwnership _out1150;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1149, out _out1150, out _out1151);
                  r = _out1149;
                  resultingOwnership = _out1150;
                  readIdents = _out1151;
                }
              } else {
                DAST._IType _3846___mcc_h1088 = _source168.dtor_baseType;
                DAST._INewtypeRange _3847___mcc_h1089 = _source168.dtor_range;
                bool _3848___mcc_h1090 = _source168.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3849___mcc_h1091 = _source168.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3850_attributes = _3849___mcc_h1091;
                bool _3851_erase = _3848___mcc_h1090;
                DAST._INewtypeRange _3852_range = _3847___mcc_h1089;
                DAST._IType _3853_b = _3846___mcc_h1088;
                {
                  RAST._IExpr _out1152;
                  DCOMP._IOwnership _out1153;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1154;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1152, out _out1153, out _out1154);
                  r = _out1152;
                  resultingOwnership = _out1153;
                  readIdents = _out1154;
                }
              }
            } else if (_source167.is_Nullable) {
              DAST._IType _3854___mcc_h1096 = _source167.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1155;
                DCOMP._IOwnership _out1156;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1155, out _out1156, out _out1157);
                r = _out1155;
                resultingOwnership = _out1156;
                readIdents = _out1157;
              }
            } else if (_source167.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3855___mcc_h1098 = _source167.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1158;
                DCOMP._IOwnership _out1159;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1158, out _out1159, out _out1160);
                r = _out1158;
                resultingOwnership = _out1159;
                readIdents = _out1160;
              }
            } else if (_source167.is_Array) {
              DAST._IType _3856___mcc_h1100 = _source167.dtor_element;
              BigInteger _3857___mcc_h1101 = _source167.dtor_dims;
              {
                RAST._IExpr _out1161;
                DCOMP._IOwnership _out1162;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1161, out _out1162, out _out1163);
                r = _out1161;
                resultingOwnership = _out1162;
                readIdents = _out1163;
              }
            } else if (_source167.is_Seq) {
              DAST._IType _3858___mcc_h1104 = _source167.dtor_element;
              {
                RAST._IExpr _out1164;
                DCOMP._IOwnership _out1165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1164, out _out1165, out _out1166);
                r = _out1164;
                resultingOwnership = _out1165;
                readIdents = _out1166;
              }
            } else if (_source167.is_Set) {
              DAST._IType _3859___mcc_h1106 = _source167.dtor_element;
              {
                RAST._IExpr _out1167;
                DCOMP._IOwnership _out1168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1167, out _out1168, out _out1169);
                r = _out1167;
                resultingOwnership = _out1168;
                readIdents = _out1169;
              }
            } else if (_source167.is_Multiset) {
              DAST._IType _3860___mcc_h1108 = _source167.dtor_element;
              {
                RAST._IExpr _out1170;
                DCOMP._IOwnership _out1171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1170, out _out1171, out _out1172);
                r = _out1170;
                resultingOwnership = _out1171;
                readIdents = _out1172;
              }
            } else if (_source167.is_Map) {
              DAST._IType _3861___mcc_h1110 = _source167.dtor_key;
              DAST._IType _3862___mcc_h1111 = _source167.dtor_value;
              {
                RAST._IExpr _out1173;
                DCOMP._IOwnership _out1174;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1173, out _out1174, out _out1175);
                r = _out1173;
                resultingOwnership = _out1174;
                readIdents = _out1175;
              }
            } else if (_source167.is_SetBuilder) {
              DAST._IType _3863___mcc_h1114 = _source167.dtor_element;
              {
                RAST._IExpr _out1176;
                DCOMP._IOwnership _out1177;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1176, out _out1177, out _out1178);
                r = _out1176;
                resultingOwnership = _out1177;
                readIdents = _out1178;
              }
            } else if (_source167.is_MapBuilder) {
              DAST._IType _3864___mcc_h1116 = _source167.dtor_key;
              DAST._IType _3865___mcc_h1117 = _source167.dtor_value;
              {
                RAST._IExpr _out1179;
                DCOMP._IOwnership _out1180;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1179, out _out1180, out _out1181);
                r = _out1179;
                resultingOwnership = _out1180;
                readIdents = _out1181;
              }
            } else if (_source167.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3866___mcc_h1120 = _source167.dtor_args;
              DAST._IType _3867___mcc_h1121 = _source167.dtor_result;
              {
                RAST._IExpr _out1182;
                DCOMP._IOwnership _out1183;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1182, out _out1183, out _out1184);
                r = _out1182;
                resultingOwnership = _out1183;
                readIdents = _out1184;
              }
            } else if (_source167.is_Primitive) {
              DAST._IPrimitive _3868___mcc_h1124 = _source167.dtor_Primitive_i_a0;
              DAST._IPrimitive _source169 = _3868___mcc_h1124;
              if (_source169.is_Int) {
                {
                  RAST._IType _3869_rhsType;
                  RAST._IType _out1185;
                  _out1185 = (this).GenType(_3215_fromTpe, true, false);
                  _3869_rhsType = _out1185;
                  RAST._IExpr _3870_recursiveGen;
                  DCOMP._IOwnership _3871___v105;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3872_recIdents;
                  RAST._IExpr _out1186;
                  DCOMP._IOwnership _out1187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1188;
                  (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1186, out _out1187, out _out1188);
                  _3870_recursiveGen = _out1186;
                  _3871___v105 = _out1187;
                  _3872_recIdents = _out1188;
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_3870_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out1189;
                  DCOMP._IOwnership _out1190;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1189, out _out1190);
                  r = _out1189;
                  resultingOwnership = _out1190;
                  readIdents = _3872_recIdents;
                }
              } else if (_source169.is_Real) {
                {
                  RAST._IExpr _out1191;
                  DCOMP._IOwnership _out1192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1191, out _out1192, out _out1193);
                  r = _out1191;
                  resultingOwnership = _out1192;
                  readIdents = _out1193;
                }
              } else if (_source169.is_String) {
                {
                  RAST._IExpr _out1194;
                  DCOMP._IOwnership _out1195;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1194, out _out1195, out _out1196);
                  r = _out1194;
                  resultingOwnership = _out1195;
                  readIdents = _out1196;
                }
              } else if (_source169.is_Bool) {
                {
                  RAST._IExpr _out1197;
                  DCOMP._IOwnership _out1198;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1197, out _out1198, out _out1199);
                  r = _out1197;
                  resultingOwnership = _out1198;
                  readIdents = _out1199;
                }
              } else {
                {
                  RAST._IExpr _out1200;
                  DCOMP._IOwnership _out1201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1200, out _out1201, out _out1202);
                  r = _out1200;
                  resultingOwnership = _out1201;
                  readIdents = _out1202;
                }
              }
            } else if (_source167.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3873___mcc_h1126 = _source167.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1203;
                DCOMP._IOwnership _out1204;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1205;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1203, out _out1204, out _out1205);
                r = _out1203;
                resultingOwnership = _out1204;
                readIdents = _out1205;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3874___mcc_h1128 = _source167.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1206;
                DCOMP._IOwnership _out1207;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1208;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1206, out _out1207, out _out1208);
                r = _out1206;
                resultingOwnership = _out1207;
                readIdents = _out1208;
              }
            }
          }
        } else if (_source128.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3875___mcc_h1130 = _source128.dtor_Passthrough_i_a0;
          DAST._IType _source170 = _3221___mcc_h1;
          if (_source170.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3876___mcc_h1134 = _source170.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3877___mcc_h1135 = _source170.dtor_typeArgs;
            DAST._IResolvedType _3878___mcc_h1136 = _source170.dtor_resolved;
            DAST._IResolvedType _source171 = _3878___mcc_h1136;
            if (_source171.is_Datatype) {
              DAST._IDatatypeType _3879___mcc_h1140 = _source171.dtor_datatypeType;
              {
                RAST._IExpr _out1209;
                DCOMP._IOwnership _out1210;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1211;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1209, out _out1210, out _out1211);
                r = _out1209;
                resultingOwnership = _out1210;
                readIdents = _out1211;
              }
            } else if (_source171.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3880___mcc_h1142 = _source171.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3881___mcc_h1143 = _source171.dtor_attributes;
              {
                RAST._IExpr _out1212;
                DCOMP._IOwnership _out1213;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1212, out _out1213, out _out1214);
                r = _out1212;
                resultingOwnership = _out1213;
                readIdents = _out1214;
              }
            } else {
              DAST._IType _3882___mcc_h1146 = _source171.dtor_baseType;
              DAST._INewtypeRange _3883___mcc_h1147 = _source171.dtor_range;
              bool _3884___mcc_h1148 = _source171.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3885___mcc_h1149 = _source171.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3886_attributes = _3885___mcc_h1149;
              bool _3887_erase = _3884___mcc_h1148;
              DAST._INewtypeRange _3888_range = _3883___mcc_h1147;
              DAST._IType _3889_b = _3882___mcc_h1146;
              {
                RAST._IExpr _out1215;
                DCOMP._IOwnership _out1216;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1215, out _out1216, out _out1217);
                r = _out1215;
                resultingOwnership = _out1216;
                readIdents = _out1217;
              }
            }
          } else if (_source170.is_Nullable) {
            DAST._IType _3890___mcc_h1154 = _source170.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1218;
              DCOMP._IOwnership _out1219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1220;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1218, out _out1219, out _out1220);
              r = _out1218;
              resultingOwnership = _out1219;
              readIdents = _out1220;
            }
          } else if (_source170.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3891___mcc_h1156 = _source170.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1221;
              DCOMP._IOwnership _out1222;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1221, out _out1222, out _out1223);
              r = _out1221;
              resultingOwnership = _out1222;
              readIdents = _out1223;
            }
          } else if (_source170.is_Array) {
            DAST._IType _3892___mcc_h1158 = _source170.dtor_element;
            BigInteger _3893___mcc_h1159 = _source170.dtor_dims;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source170.is_Seq) {
            DAST._IType _3894___mcc_h1162 = _source170.dtor_element;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source170.is_Set) {
            DAST._IType _3895___mcc_h1164 = _source170.dtor_element;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source170.is_Multiset) {
            DAST._IType _3896___mcc_h1166 = _source170.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source170.is_Map) {
            DAST._IType _3897___mcc_h1168 = _source170.dtor_key;
            DAST._IType _3898___mcc_h1169 = _source170.dtor_value;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source170.is_SetBuilder) {
            DAST._IType _3899___mcc_h1172 = _source170.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source170.is_MapBuilder) {
            DAST._IType _3900___mcc_h1174 = _source170.dtor_key;
            DAST._IType _3901___mcc_h1175 = _source170.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source170.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3902___mcc_h1178 = _source170.dtor_args;
            DAST._IType _3903___mcc_h1179 = _source170.dtor_result;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source170.is_Primitive) {
            DAST._IPrimitive _3904___mcc_h1182 = _source170.dtor_Primitive_i_a0;
            DAST._IPrimitive _source172 = _3904___mcc_h1182;
            if (_source172.is_Int) {
              {
                RAST._IType _3905_rhsType;
                RAST._IType _out1248;
                _out1248 = (this).GenType(_3215_fromTpe, true, false);
                _3905_rhsType = _out1248;
                RAST._IExpr _3906_recursiveGen;
                DCOMP._IOwnership _3907___v103;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3908_recIdents;
                RAST._IExpr _out1249;
                DCOMP._IOwnership _out1250;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1249, out _out1250, out _out1251);
                _3906_recursiveGen = _out1249;
                _3907___v103 = _out1250;
                _3908_recIdents = _out1251;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3906_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1252;
                DCOMP._IOwnership _out1253;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1252, out _out1253);
                r = _out1252;
                resultingOwnership = _out1253;
                readIdents = _3908_recIdents;
              }
            } else if (_source172.is_Real) {
              {
                RAST._IExpr _out1254;
                DCOMP._IOwnership _out1255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1254, out _out1255, out _out1256);
                r = _out1254;
                resultingOwnership = _out1255;
                readIdents = _out1256;
              }
            } else if (_source172.is_String) {
              {
                RAST._IExpr _out1257;
                DCOMP._IOwnership _out1258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1257, out _out1258, out _out1259);
                r = _out1257;
                resultingOwnership = _out1258;
                readIdents = _out1259;
              }
            } else if (_source172.is_Bool) {
              {
                RAST._IExpr _out1260;
                DCOMP._IOwnership _out1261;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1262;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1260, out _out1261, out _out1262);
                r = _out1260;
                resultingOwnership = _out1261;
                readIdents = _out1262;
              }
            } else {
              {
                RAST._IExpr _out1263;
                DCOMP._IOwnership _out1264;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1263, out _out1264, out _out1265);
                r = _out1263;
                resultingOwnership = _out1264;
                readIdents = _out1265;
              }
            }
          } else if (_source170.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3909___mcc_h1184 = _source170.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _3910_recursiveGen;
              DCOMP._IOwnership _3911___v108;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3912_recIdents;
              RAST._IExpr _out1266;
              DCOMP._IOwnership _out1267;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1268;
              (this).GenExpr(_3214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1266, out _out1267, out _out1268);
              _3910_recursiveGen = _out1266;
              _3911___v108 = _out1267;
              _3912_recIdents = _out1268;
              RAST._IType _3913_toTpeGen;
              RAST._IType _out1269;
              _out1269 = (this).GenType(_3216_toTpe, true, false);
              _3913_toTpeGen = _out1269;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3910_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3913_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1270;
              DCOMP._IOwnership _out1271;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1270, out _out1271);
              r = _out1270;
              resultingOwnership = _out1271;
              readIdents = _3912_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3914___mcc_h1186 = _source170.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1272;
              DCOMP._IOwnership _out1273;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1274;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1272, out _out1273, out _out1274);
              r = _out1272;
              resultingOwnership = _out1273;
              readIdents = _out1274;
            }
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _3915___mcc_h1188 = _source128.dtor_TypeArg_i_a0;
          DAST._IType _source173 = _3221___mcc_h1;
          if (_source173.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3916___mcc_h1192 = _source173.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3917___mcc_h1193 = _source173.dtor_typeArgs;
            DAST._IResolvedType _3918___mcc_h1194 = _source173.dtor_resolved;
            DAST._IResolvedType _source174 = _3918___mcc_h1194;
            if (_source174.is_Datatype) {
              DAST._IDatatypeType _3919___mcc_h1198 = _source174.dtor_datatypeType;
              {
                RAST._IExpr _out1275;
                DCOMP._IOwnership _out1276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1277;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1275, out _out1276, out _out1277);
                r = _out1275;
                resultingOwnership = _out1276;
                readIdents = _out1277;
              }
            } else if (_source174.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3920___mcc_h1200 = _source174.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3921___mcc_h1201 = _source174.dtor_attributes;
              {
                RAST._IExpr _out1278;
                DCOMP._IOwnership _out1279;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1278, out _out1279, out _out1280);
                r = _out1278;
                resultingOwnership = _out1279;
                readIdents = _out1280;
              }
            } else {
              DAST._IType _3922___mcc_h1204 = _source174.dtor_baseType;
              DAST._INewtypeRange _3923___mcc_h1205 = _source174.dtor_range;
              bool _3924___mcc_h1206 = _source174.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3925___mcc_h1207 = _source174.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3926_attributes = _3925___mcc_h1207;
              bool _3927_erase = _3924___mcc_h1206;
              DAST._INewtypeRange _3928_range = _3923___mcc_h1205;
              DAST._IType _3929_b = _3922___mcc_h1204;
              {
                RAST._IExpr _out1281;
                DCOMP._IOwnership _out1282;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1283;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1281, out _out1282, out _out1283);
                r = _out1281;
                resultingOwnership = _out1282;
                readIdents = _out1283;
              }
            }
          } else if (_source173.is_Nullable) {
            DAST._IType _3930___mcc_h1212 = _source173.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1284;
              DCOMP._IOwnership _out1285;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1286;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1284, out _out1285, out _out1286);
              r = _out1284;
              resultingOwnership = _out1285;
              readIdents = _out1286;
            }
          } else if (_source173.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3931___mcc_h1214 = _source173.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1287;
              DCOMP._IOwnership _out1288;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1289;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1287, out _out1288, out _out1289);
              r = _out1287;
              resultingOwnership = _out1288;
              readIdents = _out1289;
            }
          } else if (_source173.is_Array) {
            DAST._IType _3932___mcc_h1216 = _source173.dtor_element;
            BigInteger _3933___mcc_h1217 = _source173.dtor_dims;
            {
              RAST._IExpr _out1290;
              DCOMP._IOwnership _out1291;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1290, out _out1291, out _out1292);
              r = _out1290;
              resultingOwnership = _out1291;
              readIdents = _out1292;
            }
          } else if (_source173.is_Seq) {
            DAST._IType _3934___mcc_h1220 = _source173.dtor_element;
            {
              RAST._IExpr _out1293;
              DCOMP._IOwnership _out1294;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1295;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1293, out _out1294, out _out1295);
              r = _out1293;
              resultingOwnership = _out1294;
              readIdents = _out1295;
            }
          } else if (_source173.is_Set) {
            DAST._IType _3935___mcc_h1222 = _source173.dtor_element;
            {
              RAST._IExpr _out1296;
              DCOMP._IOwnership _out1297;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1298;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1296, out _out1297, out _out1298);
              r = _out1296;
              resultingOwnership = _out1297;
              readIdents = _out1298;
            }
          } else if (_source173.is_Multiset) {
            DAST._IType _3936___mcc_h1224 = _source173.dtor_element;
            {
              RAST._IExpr _out1299;
              DCOMP._IOwnership _out1300;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1299, out _out1300, out _out1301);
              r = _out1299;
              resultingOwnership = _out1300;
              readIdents = _out1301;
            }
          } else if (_source173.is_Map) {
            DAST._IType _3937___mcc_h1226 = _source173.dtor_key;
            DAST._IType _3938___mcc_h1227 = _source173.dtor_value;
            {
              RAST._IExpr _out1302;
              DCOMP._IOwnership _out1303;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1304;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1302, out _out1303, out _out1304);
              r = _out1302;
              resultingOwnership = _out1303;
              readIdents = _out1304;
            }
          } else if (_source173.is_SetBuilder) {
            DAST._IType _3939___mcc_h1230 = _source173.dtor_element;
            {
              RAST._IExpr _out1305;
              DCOMP._IOwnership _out1306;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1307;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1305, out _out1306, out _out1307);
              r = _out1305;
              resultingOwnership = _out1306;
              readIdents = _out1307;
            }
          } else if (_source173.is_MapBuilder) {
            DAST._IType _3940___mcc_h1232 = _source173.dtor_key;
            DAST._IType _3941___mcc_h1233 = _source173.dtor_value;
            {
              RAST._IExpr _out1308;
              DCOMP._IOwnership _out1309;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1310;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1308, out _out1309, out _out1310);
              r = _out1308;
              resultingOwnership = _out1309;
              readIdents = _out1310;
            }
          } else if (_source173.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3942___mcc_h1236 = _source173.dtor_args;
            DAST._IType _3943___mcc_h1237 = _source173.dtor_result;
            {
              RAST._IExpr _out1311;
              DCOMP._IOwnership _out1312;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1311, out _out1312, out _out1313);
              r = _out1311;
              resultingOwnership = _out1312;
              readIdents = _out1313;
            }
          } else if (_source173.is_Primitive) {
            DAST._IPrimitive _3944___mcc_h1240 = _source173.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out1314;
              DCOMP._IOwnership _out1315;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1314, out _out1315, out _out1316);
              r = _out1314;
              resultingOwnership = _out1315;
              readIdents = _out1316;
            }
          } else if (_source173.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3945___mcc_h1242 = _source173.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out1317;
              DCOMP._IOwnership _out1318;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1319;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1317, out _out1318, out _out1319);
              r = _out1317;
              resultingOwnership = _out1318;
              readIdents = _out1319;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3946___mcc_h1244 = _source173.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1320;
              DCOMP._IOwnership _out1321;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1320, out _out1321, out _out1322);
              r = _out1320;
              resultingOwnership = _out1321;
              readIdents = _out1322;
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
      Std.Wrappers._IOption<RAST._IType> _3947_tpe;
      _3947_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _3948_placeboOpt;
      _3948_placeboOpt = (((_3947_tpe).is_Some) ? (((_3947_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _3949_currentlyBorrowed;
      _3949_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3950_noNeedOfClone;
      _3950_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_3948_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _3949_currentlyBorrowed = false;
        _3950_noNeedOfClone = true;
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_3950_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3950_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_3949_currentlyBorrowed) {
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
      DAST._IExpression _source175 = e;
      if (_source175.is_Literal) {
        DAST._ILiteral _3951___mcc_h0 = _source175.dtor_Literal_i_a0;
        RAST._IExpr _out1323;
        DCOMP._IOwnership _out1324;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1325;
        (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out1323, out _out1324, out _out1325);
        r = _out1323;
        resultingOwnership = _out1324;
        readIdents = _out1325;
      } else if (_source175.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3952___mcc_h1 = _source175.dtor_Ident_i_a0;
        Dafny.ISequence<Dafny.Rune> _3953_name = _3952___mcc_h1;
        {
          RAST._IExpr _out1326;
          DCOMP._IOwnership _out1327;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1328;
          (this).GenIdent(DCOMP.__default.escapeName(_3953_name), selfIdent, env, expectedOwnership, out _out1326, out _out1327, out _out1328);
          r = _out1326;
          resultingOwnership = _out1327;
          readIdents = _out1328;
        }
      } else if (_source175.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3954___mcc_h2 = _source175.dtor_Companion_i_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3955_path = _3954___mcc_h2;
        {
          RAST._IExpr _out1329;
          _out1329 = DCOMP.COMP.GenPathExpr(_3955_path);
          r = _out1329;
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else {
            RAST._IExpr _out1330;
            DCOMP._IOwnership _out1331;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1330, out _out1331);
            r = _out1330;
            resultingOwnership = _out1331;
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3956___mcc_h3 = _source175.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IExpression> _3957_values = _3956___mcc_h3;
        {
          Dafny.ISequence<RAST._IExpr> _3958_exprs;
          _3958_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi30 = new BigInteger((_3957_values).Count);
          for (BigInteger _3959_i = BigInteger.Zero; _3959_i < _hi30; _3959_i++) {
            RAST._IExpr _3960_recursiveGen;
            DCOMP._IOwnership _3961___v111;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3962_recIdents;
            RAST._IExpr _out1332;
            DCOMP._IOwnership _out1333;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
            (this).GenExpr((_3957_values).Select(_3959_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1332, out _out1333, out _out1334);
            _3960_recursiveGen = _out1332;
            _3961___v111 = _out1333;
            _3962_recIdents = _out1334;
            _3958_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_3958_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3960_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3962_recIdents);
          }
          r = RAST.Expr.create_Tuple(_3958_exprs);
          RAST._IExpr _out1335;
          DCOMP._IOwnership _out1336;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1335, out _out1336);
          r = _out1335;
          resultingOwnership = _out1336;
          return ;
        }
      } else if (_source175.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3963___mcc_h4 = _source175.dtor_path;
        Dafny.ISequence<DAST._IType> _3964___mcc_h5 = _source175.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3965___mcc_h6 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3966_args = _3965___mcc_h6;
        Dafny.ISequence<DAST._IType> _3967_typeArgs = _3964___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3968_path = _3963___mcc_h4;
        {
          RAST._IExpr _out1337;
          _out1337 = DCOMP.COMP.GenPathExpr(_3968_path);
          r = _out1337;
          if ((new BigInteger((_3967_typeArgs).Count)).Sign == 1) {
            Dafny.ISequence<RAST._IType> _3969_typeExprs;
            _3969_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi31 = new BigInteger((_3967_typeArgs).Count);
            for (BigInteger _3970_i = BigInteger.Zero; _3970_i < _hi31; _3970_i++) {
              RAST._IType _3971_typeExpr;
              RAST._IType _out1338;
              _out1338 = (this).GenType((_3967_typeArgs).Select(_3970_i), false, false);
              _3971_typeExpr = _out1338;
              _3969_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3969_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3971_typeExpr));
            }
            r = (r).ApplyType(_3969_typeExprs);
          }
          r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_allocated"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IExpr> _3972_arguments;
          _3972_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_3966_args).Count);
          for (BigInteger _3973_i = BigInteger.Zero; _3973_i < _hi32; _3973_i++) {
            RAST._IExpr _3974_recursiveGen;
            DCOMP._IOwnership _3975___v112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3976_recIdents;
            RAST._IExpr _out1339;
            DCOMP._IOwnership _out1340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
            (this).GenExpr((_3966_args).Select(_3973_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1339, out _out1340, out _out1341);
            _3974_recursiveGen = _out1339;
            _3975___v112 = _out1340;
            _3976_recIdents = _out1341;
            _3972_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3972_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3974_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3976_recIdents);
          }
          r = (r).Apply(_3972_arguments);
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1342, out _out1343);
          r = _out1342;
          resultingOwnership = _out1343;
          return ;
        }
      } else if (_source175.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3977___mcc_h7 = _source175.dtor_dims;
        DAST._IType _3978___mcc_h8 = _source175.dtor_typ;
        DAST._IType _3979_typ = _3978___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3980_dims = _3977___mcc_h7;
        {
          BigInteger _3981_i;
          _3981_i = (new BigInteger((_3980_dims).Count)) - (BigInteger.One);
          RAST._IType _3982_genTyp;
          RAST._IType _out1344;
          _out1344 = (this).GenType(_3979_typ, false, false);
          _3982_genTyp = _out1344;
          Dafny.ISequence<Dafny.Rune> _3983_s;
          _3983_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3982_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3981_i).Sign != -1) {
            RAST._IExpr _3984_recursiveGen;
            DCOMP._IOwnership _3985___v113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3986_recIdents;
            RAST._IExpr _out1345;
            DCOMP._IOwnership _out1346;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1347;
            (this).GenExpr((_3980_dims).Select(_3981_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1345, out _out1346, out _out1347);
            _3984_recursiveGen = _out1345;
            _3985___v113 = _out1346;
            _3986_recIdents = _out1347;
            _3983_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3983_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3984_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3986_recIdents);
            _3981_i = (_3981_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3983_s);
          RAST._IExpr _out1348;
          DCOMP._IOwnership _out1349;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1348, out _out1349);
          r = _out1348;
          resultingOwnership = _out1349;
        }
      } else if (_source175.is_DatatypeValue) {
        DAST._IDatatypeType _3987___mcc_h9 = _source175.dtor_datatypeType;
        Dafny.ISequence<DAST._IType> _3988___mcc_h10 = _source175.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3989___mcc_h11 = _source175.dtor_variant;
        bool _3990___mcc_h12 = _source175.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3991___mcc_h13 = _source175.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3992_values = _3991___mcc_h13;
        bool _3993_isCo = _3990___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3994_variant = _3989___mcc_h11;
        Dafny.ISequence<DAST._IType> _3995_typeArgs = _3988___mcc_h10;
        DAST._IDatatypeType _3996_datatypeType = _3987___mcc_h9;
        {
          RAST._IExpr _out1350;
          _out1350 = DCOMP.COMP.GenPathExpr((_3996_datatypeType).dtor_path);
          r = _out1350;
          Dafny.ISequence<RAST._IType> _3997_genTypeArgs;
          _3997_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _hi33 = new BigInteger((_3995_typeArgs).Count);
          for (BigInteger _3998_i = BigInteger.Zero; _3998_i < _hi33; _3998_i++) {
            RAST._IType _3999_typeExpr;
            RAST._IType _out1351;
            _out1351 = (this).GenType((_3995_typeArgs).Select(_3998_i), false, false);
            _3999_typeExpr = _out1351;
            _3997_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_3997_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_3999_typeExpr));
          }
          if ((new BigInteger((_3995_typeArgs).Count)).Sign == 1) {
            r = (r).ApplyType(_3997_genTypeArgs);
          }
          r = (r).MSel(DCOMP.__default.escapeName(_3994_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IAssignIdentifier> _4000_assignments;
          _4000_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
          BigInteger _hi34 = new BigInteger((_3992_values).Count);
          for (BigInteger _4001_i = BigInteger.Zero; _4001_i < _hi34; _4001_i++) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_3992_values).Select(_4001_i);
            Dafny.ISequence<Dafny.Rune> _4002_name = _let_tmp_rhs63.dtor__0;
            DAST._IExpression _4003_value = _let_tmp_rhs63.dtor__1;
            if (_3993_isCo) {
              RAST._IExpr _4004_recursiveGen;
              DCOMP._IOwnership _4005___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4006_recIdents;
              RAST._IExpr _out1352;
              DCOMP._IOwnership _out1353;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
              (this).GenExpr(_4003_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out1352, out _out1353, out _out1354);
              _4004_recursiveGen = _out1352;
              _4005___v114 = _out1353;
              _4006_recIdents = _out1354;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4006_recIdents);
              Dafny.ISequence<Dafny.Rune> _4007_allReadCloned;
              _4007_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_4006_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _4008_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_4006_recIdents).Elements) {
                  _4008_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_4006_recIdents).Contains(_4008_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 3275)");
              after__ASSIGN_SUCH_THAT_2: ;
                _4007_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4007_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _4008_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _4008_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _4006_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4006_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4008_next));
              }
              Dafny.ISequence<Dafny.Rune> _4009_wasAssigned;
              _4009_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _4007_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_4004_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              _4000_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_4000_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_4002_name, RAST.Expr.create_RawExpr(_4009_wasAssigned))));
            } else {
              RAST._IExpr _4010_recursiveGen;
              DCOMP._IOwnership _4011___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4012_recIdents;
              RAST._IExpr _out1355;
              DCOMP._IOwnership _out1356;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1357;
              (this).GenExpr(_4003_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1355, out _out1356, out _out1357);
              _4010_recursiveGen = _out1355;
              _4011___v115 = _out1356;
              _4012_recIdents = _out1357;
              _4000_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_4000_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_4002_name, _4010_recursiveGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4012_recIdents);
            }
          }
          r = RAST.Expr.create_StructBuild(r, _4000_assignments);
          r = RAST.__default.RcNew(r);
          RAST._IExpr _out1358;
          DCOMP._IOwnership _out1359;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1358, out _out1359);
          r = _out1358;
          resultingOwnership = _out1359;
          return ;
        }
      } else if (_source175.is_Convert) {
        DAST._IExpression _4013___mcc_h14 = _source175.dtor_value;
        DAST._IType _4014___mcc_h15 = _source175.dtor_from;
        DAST._IType _4015___mcc_h16 = _source175.dtor_typ;
        {
          RAST._IExpr _out1360;
          DCOMP._IOwnership _out1361;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
          (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out1360, out _out1361, out _out1362);
          r = _out1360;
          resultingOwnership = _out1361;
          readIdents = _out1362;
        }
      } else if (_source175.is_SeqConstruct) {
        DAST._IExpression _4016___mcc_h17 = _source175.dtor_length;
        DAST._IExpression _4017___mcc_h18 = _source175.dtor_elem;
        DAST._IExpression _4018_expr = _4017___mcc_h18;
        DAST._IExpression _4019_length = _4016___mcc_h17;
        {
          RAST._IExpr _4020_recursiveGen;
          DCOMP._IOwnership _4021___v119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4022_recIdents;
          RAST._IExpr _out1363;
          DCOMP._IOwnership _out1364;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1365;
          (this).GenExpr(_4018_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1363, out _out1364, out _out1365);
          _4020_recursiveGen = _out1363;
          _4021___v119 = _out1364;
          _4022_recIdents = _out1365;
          RAST._IExpr _4023_lengthGen;
          DCOMP._IOwnership _4024___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4025_lengthIdents;
          RAST._IExpr _out1366;
          DCOMP._IOwnership _out1367;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1368;
          (this).GenExpr(_4019_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1366, out _out1367, out _out1368);
          _4023_lengthGen = _out1366;
          _4024___v120 = _out1367;
          _4025_lengthIdents = _out1368;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_4020_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_4023_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4022_recIdents, _4025_lengthIdents);
          RAST._IExpr _out1369;
          DCOMP._IOwnership _out1370;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1369, out _out1370);
          r = _out1369;
          resultingOwnership = _out1370;
          return ;
        }
      } else if (_source175.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _4026___mcc_h19 = _source175.dtor_elements;
        DAST._IType _4027___mcc_h20 = _source175.dtor_typ;
        DAST._IType _4028_typ = _4027___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _4029_exprs = _4026___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _4030_genTpe;
          RAST._IType _out1371;
          _out1371 = (this).GenType(_4028_typ, false, false);
          _4030_genTpe = _out1371;
          BigInteger _4031_i;
          _4031_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4032_args;
          _4032_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4031_i) < (new BigInteger((_4029_exprs).Count))) {
            RAST._IExpr _4033_recursiveGen;
            DCOMP._IOwnership _4034___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4035_recIdents;
            RAST._IExpr _out1372;
            DCOMP._IOwnership _out1373;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
            (this).GenExpr((_4029_exprs).Select(_4031_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1372, out _out1373, out _out1374);
            _4033_recursiveGen = _out1372;
            _4034___v121 = _out1373;
            _4035_recIdents = _out1374;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4035_recIdents);
            _4032_args = Dafny.Sequence<RAST._IExpr>.Concat(_4032_args, Dafny.Sequence<RAST._IExpr>.FromElements(_4033_recursiveGen));
            _4031_i = (_4031_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_4032_args);
          if ((new BigInteger((_4032_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_4030_genTpe));
          }
          RAST._IExpr _out1375;
          DCOMP._IOwnership _out1376;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1375, out _out1376);
          r = _out1375;
          resultingOwnership = _out1376;
          return ;
        }
      } else if (_source175.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _4036___mcc_h21 = _source175.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4037_exprs = _4036___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _4038_generatedValues;
          _4038_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4039_i;
          _4039_i = BigInteger.Zero;
          while ((_4039_i) < (new BigInteger((_4037_exprs).Count))) {
            RAST._IExpr _4040_recursiveGen;
            DCOMP._IOwnership _4041___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4042_recIdents;
            RAST._IExpr _out1377;
            DCOMP._IOwnership _out1378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
            (this).GenExpr((_4037_exprs).Select(_4039_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1377, out _out1378, out _out1379);
            _4040_recursiveGen = _out1377;
            _4041___v122 = _out1378;
            _4042_recIdents = _out1379;
            _4038_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4038_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4040_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4042_recIdents);
            _4039_i = (_4039_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_4038_generatedValues);
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          return ;
        }
      } else if (_source175.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _4043___mcc_h22 = _source175.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _4044_exprs = _4043___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _4045_generatedValues;
          _4045_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4046_i;
          _4046_i = BigInteger.Zero;
          while ((_4046_i) < (new BigInteger((_4044_exprs).Count))) {
            RAST._IExpr _4047_recursiveGen;
            DCOMP._IOwnership _4048___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4049_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr((_4044_exprs).Select(_4046_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _4047_recursiveGen = _out1382;
            _4048___v123 = _out1383;
            _4049_recIdents = _out1384;
            _4045_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_4045_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_4047_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4049_recIdents);
            _4046_i = (_4046_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_4045_generatedValues);
          RAST._IExpr _out1385;
          DCOMP._IOwnership _out1386;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
          r = _out1385;
          resultingOwnership = _out1386;
          return ;
        }
      } else if (_source175.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4050___mcc_h23 = _source175.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4051_mapElems = _4050___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _4052_generatedValues;
          _4052_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4053_i;
          _4053_i = BigInteger.Zero;
          while ((_4053_i) < (new BigInteger((_4051_mapElems).Count))) {
            RAST._IExpr _4054_recursiveGenKey;
            DCOMP._IOwnership _4055___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4056_recIdentsKey;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(((_4051_mapElems).Select(_4053_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _4054_recursiveGenKey = _out1387;
            _4055___v125 = _out1388;
            _4056_recIdentsKey = _out1389;
            RAST._IExpr _4057_recursiveGenValue;
            DCOMP._IOwnership _4058___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4059_recIdentsValue;
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1392;
            (this).GenExpr(((_4051_mapElems).Select(_4053_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1390, out _out1391, out _out1392);
            _4057_recursiveGenValue = _out1390;
            _4058___v126 = _out1391;
            _4059_recIdentsValue = _out1392;
            _4052_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_4052_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_4054_recursiveGenKey, _4057_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4056_recIdentsKey), _4059_recIdentsValue);
            _4053_i = (_4053_i) + (BigInteger.One);
          }
          _4053_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _4060_arguments;
          _4060_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_4053_i) < (new BigInteger((_4052_generatedValues).Count))) {
            RAST._IExpr _4061_genKey;
            _4061_genKey = ((_4052_generatedValues).Select(_4053_i)).dtor__0;
            RAST._IExpr _4062_genValue;
            _4062_genValue = ((_4052_generatedValues).Select(_4053_i)).dtor__1;
            _4060_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4060_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _4061_genKey, _4062_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _4053_i = (_4053_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_4060_arguments);
          RAST._IExpr _out1393;
          DCOMP._IOwnership _out1394;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1393, out _out1394);
          r = _out1393;
          resultingOwnership = _out1394;
          return ;
        }
      } else if (_source175.is_MapBuilder) {
        DAST._IType _4063___mcc_h24 = _source175.dtor_keyType;
        DAST._IType _4064___mcc_h25 = _source175.dtor_valueType;
        DAST._IType _4065_valueType = _4064___mcc_h25;
        DAST._IType _4066_keyType = _4063___mcc_h24;
        {
          RAST._IType _4067_kType;
          RAST._IType _out1395;
          _out1395 = (this).GenType(_4066_keyType, false, false);
          _4067_kType = _out1395;
          RAST._IType _4068_vType;
          RAST._IType _out1396;
          _out1396 = (this).GenType(_4065_valueType, false, false);
          _4068_vType = _out1396;
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4067_kType, _4068_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1397;
          DCOMP._IOwnership _out1398;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1397, out _out1398);
          r = _out1397;
          resultingOwnership = _out1398;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_SeqUpdate) {
        DAST._IExpression _4069___mcc_h26 = _source175.dtor_expr;
        DAST._IExpression _4070___mcc_h27 = _source175.dtor_indexExpr;
        DAST._IExpression _4071___mcc_h28 = _source175.dtor_value;
        DAST._IExpression _4072_value = _4071___mcc_h28;
        DAST._IExpression _4073_index = _4070___mcc_h27;
        DAST._IExpression _4074_expr = _4069___mcc_h26;
        {
          RAST._IExpr _4075_exprR;
          DCOMP._IOwnership _4076___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4077_exprIdents;
          RAST._IExpr _out1399;
          DCOMP._IOwnership _out1400;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1401;
          (this).GenExpr(_4074_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1399, out _out1400, out _out1401);
          _4075_exprR = _out1399;
          _4076___v127 = _out1400;
          _4077_exprIdents = _out1401;
          RAST._IExpr _4078_indexR;
          DCOMP._IOwnership _4079_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4080_indexIdents;
          RAST._IExpr _out1402;
          DCOMP._IOwnership _out1403;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1404;
          (this).GenExpr(_4073_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1402, out _out1403, out _out1404);
          _4078_indexR = _out1402;
          _4079_indexOwnership = _out1403;
          _4080_indexIdents = _out1404;
          RAST._IExpr _4081_valueR;
          DCOMP._IOwnership _4082_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4083_valueIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_4072_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1405, out _out1406, out _out1407);
          _4081_valueR = _out1405;
          _4082_valueOwnership = _out1406;
          _4083_valueIdents = _out1407;
          r = ((_4075_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4078_indexR, _4081_valueR));
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4077_exprIdents, _4080_indexIdents), _4083_valueIdents);
          return ;
        }
      } else if (_source175.is_MapUpdate) {
        DAST._IExpression _4084___mcc_h29 = _source175.dtor_expr;
        DAST._IExpression _4085___mcc_h30 = _source175.dtor_indexExpr;
        DAST._IExpression _4086___mcc_h31 = _source175.dtor_value;
        DAST._IExpression _4087_value = _4086___mcc_h31;
        DAST._IExpression _4088_index = _4085___mcc_h30;
        DAST._IExpression _4089_expr = _4084___mcc_h29;
        {
          RAST._IExpr _4090_exprR;
          DCOMP._IOwnership _4091___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4092_exprIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_4089_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1410, out _out1411, out _out1412);
          _4090_exprR = _out1410;
          _4091___v128 = _out1411;
          _4092_exprIdents = _out1412;
          RAST._IExpr _4093_indexR;
          DCOMP._IOwnership _4094_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4095_indexIdents;
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1415;
          (this).GenExpr(_4088_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1413, out _out1414, out _out1415);
          _4093_indexR = _out1413;
          _4094_indexOwnership = _out1414;
          _4095_indexIdents = _out1415;
          RAST._IExpr _4096_valueR;
          DCOMP._IOwnership _4097_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4098_valueIdents;
          RAST._IExpr _out1416;
          DCOMP._IOwnership _out1417;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
          (this).GenExpr(_4087_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1416, out _out1417, out _out1418);
          _4096_valueR = _out1416;
          _4097_valueOwnership = _out1417;
          _4098_valueIdents = _out1418;
          r = ((_4090_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4093_indexR, _4096_valueR));
          RAST._IExpr _out1419;
          DCOMP._IOwnership _out1420;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1419, out _out1420);
          r = _out1419;
          resultingOwnership = _out1420;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4092_exprIdents, _4095_indexIdents), _4098_valueIdents);
          return ;
        }
      } else if (_source175.is_SetBuilder) {
        DAST._IType _4099___mcc_h32 = _source175.dtor_elemType;
        DAST._IType _4100_elemType = _4099___mcc_h32;
        {
          RAST._IType _4101_eType;
          RAST._IType _out1421;
          _out1421 = (this).GenType(_4100_elemType, false, false);
          _4101_eType = _out1421;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4101_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1422;
          DCOMP._IOwnership _out1423;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1422, out _out1423);
          r = _out1422;
          resultingOwnership = _out1423;
          return ;
        }
      } else if (_source175.is_ToMultiset) {
        DAST._IExpression _4102___mcc_h33 = _source175.dtor_ToMultiset_i_a0;
        DAST._IExpression _4103_expr = _4102___mcc_h33;
        {
          RAST._IExpr _4104_recursiveGen;
          DCOMP._IOwnership _4105___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4106_recIdents;
          RAST._IExpr _out1424;
          DCOMP._IOwnership _out1425;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
          (this).GenExpr(_4103_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1424, out _out1425, out _out1426);
          _4104_recursiveGen = _out1424;
          _4105___v124 = _out1425;
          _4106_recIdents = _out1426;
          r = ((_4104_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _4106_recIdents;
          RAST._IExpr _out1427;
          DCOMP._IOwnership _out1428;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1427, out _out1428);
          r = _out1427;
          resultingOwnership = _out1428;
          return ;
        }
      } else if (_source175.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source176 = selfIdent;
          if (_source176.is_None) {
            {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
              RAST._IExpr _out1429;
              DCOMP._IOwnership _out1430;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1429, out _out1430);
              r = _out1429;
              resultingOwnership = _out1430;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _4107___mcc_h288 = _source176.dtor_value;
            Dafny.ISequence<Dafny.Rune> _4108_id = _4107___mcc_h288;
            {
              r = RAST.Expr.create_Identifier(_4108_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_4108_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_4108_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4108_id);
            }
          }
          return ;
        }
      } else if (_source175.is_Ite) {
        DAST._IExpression _4109___mcc_h34 = _source175.dtor_cond;
        DAST._IExpression _4110___mcc_h35 = _source175.dtor_thn;
        DAST._IExpression _4111___mcc_h36 = _source175.dtor_els;
        DAST._IExpression _4112_f = _4111___mcc_h36;
        DAST._IExpression _4113_t = _4110___mcc_h35;
        DAST._IExpression _4114_cond = _4109___mcc_h34;
        {
          RAST._IExpr _4115_cond;
          DCOMP._IOwnership _4116___v129;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4117_recIdentsCond;
          RAST._IExpr _out1431;
          DCOMP._IOwnership _out1432;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1433;
          (this).GenExpr(_4114_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1431, out _out1432, out _out1433);
          _4115_cond = _out1431;
          _4116___v129 = _out1432;
          _4117_recIdentsCond = _out1433;
          Dafny.ISequence<Dafny.Rune> _4118_condString;
          _4118_condString = (_4115_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4119___v130;
          DCOMP._IOwnership _4120_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4121___v131;
          RAST._IExpr _out1434;
          DCOMP._IOwnership _out1435;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
          (this).GenExpr(_4113_t, selfIdent, env, expectedOwnership, out _out1434, out _out1435, out _out1436);
          _4119___v130 = _out1434;
          _4120_tHasToBeOwned = _out1435;
          _4121___v131 = _out1436;
          RAST._IExpr _4122_fExpr;
          DCOMP._IOwnership _4123_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4124_recIdentsF;
          RAST._IExpr _out1437;
          DCOMP._IOwnership _out1438;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1439;
          (this).GenExpr(_4112_f, selfIdent, env, _4120_tHasToBeOwned, out _out1437, out _out1438, out _out1439);
          _4122_fExpr = _out1437;
          _4123_fOwned = _out1438;
          _4124_recIdentsF = _out1439;
          Dafny.ISequence<Dafny.Rune> _4125_fString;
          _4125_fString = (_4122_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4126_tExpr;
          DCOMP._IOwnership _4127___v132;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4128_recIdentsT;
          RAST._IExpr _out1440;
          DCOMP._IOwnership _out1441;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
          (this).GenExpr(_4113_t, selfIdent, env, _4123_fOwned, out _out1440, out _out1441, out _out1442);
          _4126_tExpr = _out1440;
          _4127___v132 = _out1441;
          _4128_recIdentsT = _out1442;
          Dafny.ISequence<Dafny.Rune> _4129_tString;
          _4129_tString = (_4126_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _4118_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _4129_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _4125_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1443;
          DCOMP._IOwnership _out1444;
          DCOMP.COMP.FromOwnership(r, _4123_fOwned, expectedOwnership, out _out1443, out _out1444);
          r = _out1443;
          resultingOwnership = _out1444;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4117_recIdentsCond, _4128_recIdentsT), _4124_recIdentsF);
          return ;
        }
      } else if (_source175.is_UnOp) {
        DAST._IUnaryOp _4130___mcc_h37 = _source175.dtor_unOp;
        DAST._IExpression _4131___mcc_h38 = _source175.dtor_expr;
        DAST.Format._IUnaryOpFormat _4132___mcc_h39 = _source175.dtor_format1;
        DAST._IUnaryOp _source177 = _4130___mcc_h37;
        if (_source177.is_Not) {
          DAST.Format._IUnaryOpFormat _4133_format = _4132___mcc_h39;
          DAST._IExpression _4134_e = _4131___mcc_h38;
          {
            RAST._IExpr _4135_recursiveGen;
            DCOMP._IOwnership _4136___v133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4137_recIdents;
            RAST._IExpr _out1445;
            DCOMP._IOwnership _out1446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1447;
            (this).GenExpr(_4134_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1445, out _out1446, out _out1447);
            _4135_recursiveGen = _out1445;
            _4136___v133 = _out1446;
            _4137_recIdents = _out1447;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _4135_recursiveGen, _4133_format);
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1448, out _out1449);
            r = _out1448;
            resultingOwnership = _out1449;
            readIdents = _4137_recIdents;
            return ;
          }
        } else if (_source177.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _4138_format = _4132___mcc_h39;
          DAST._IExpression _4139_e = _4131___mcc_h38;
          {
            RAST._IExpr _4140_recursiveGen;
            DCOMP._IOwnership _4141___v134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4142_recIdents;
            RAST._IExpr _out1450;
            DCOMP._IOwnership _out1451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1452;
            (this).GenExpr(_4139_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1450, out _out1451, out _out1452);
            _4140_recursiveGen = _out1450;
            _4141___v134 = _out1451;
            _4142_recIdents = _out1452;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _4140_recursiveGen, _4138_format);
            RAST._IExpr _out1453;
            DCOMP._IOwnership _out1454;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1453, out _out1454);
            r = _out1453;
            resultingOwnership = _out1454;
            readIdents = _4142_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _4143_format = _4132___mcc_h39;
          DAST._IExpression _4144_e = _4131___mcc_h38;
          {
            RAST._IExpr _4145_recursiveGen;
            DCOMP._IOwnership _4146_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4147_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_4144_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1455, out _out1456, out _out1457);
            _4145_recursiveGen = _out1455;
            _4146_recOwned = _out1456;
            _4147_recIdents = _out1457;
            r = ((_4145_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1458;
            DCOMP._IOwnership _out1459;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
            r = _out1458;
            resultingOwnership = _out1459;
            readIdents = _4147_recIdents;
            return ;
          }
        }
      } else if (_source175.is_BinOp) {
        DAST._IBinOp _4148___mcc_h40 = _source175.dtor_op;
        DAST._IExpression _4149___mcc_h41 = _source175.dtor_left;
        DAST._IExpression _4150___mcc_h42 = _source175.dtor_right;
        DAST.Format._IBinaryOpFormat _4151___mcc_h43 = _source175.dtor_format2;
        RAST._IExpr _out1460;
        DCOMP._IOwnership _out1461;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
        (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out1460, out _out1461, out _out1462);
        r = _out1460;
        resultingOwnership = _out1461;
        readIdents = _out1462;
      } else if (_source175.is_ArrayLen) {
        DAST._IExpression _4152___mcc_h44 = _source175.dtor_expr;
        BigInteger _4153___mcc_h45 = _source175.dtor_dim;
        BigInteger _4154_dim = _4153___mcc_h45;
        DAST._IExpression _4155_expr = _4152___mcc_h44;
        {
          RAST._IExpr _4156_recursiveGen;
          DCOMP._IOwnership _4157___v139;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4158_recIdents;
          RAST._IExpr _out1463;
          DCOMP._IOwnership _out1464;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1465;
          (this).GenExpr(_4155_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1463, out _out1464, out _out1465);
          _4156_recursiveGen = _out1463;
          _4157___v139 = _out1464;
          _4158_recIdents = _out1465;
          if ((_4154_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_4156_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _4159_s;
            _4159_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _4160_i;
            _4160_i = BigInteger.One;
            while ((_4160_i) < (_4154_dim)) {
              _4159_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _4159_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _4160_i = (_4160_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4156_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _4159_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1466;
          DCOMP._IOwnership _out1467;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1466, out _out1467);
          r = _out1466;
          resultingOwnership = _out1467;
          readIdents = _4158_recIdents;
          return ;
        }
      } else if (_source175.is_MapKeys) {
        DAST._IExpression _4161___mcc_h46 = _source175.dtor_expr;
        DAST._IExpression _4162_expr = _4161___mcc_h46;
        {
          RAST._IExpr _4163_recursiveGen;
          DCOMP._IOwnership _4164___v140;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4165_recIdents;
          RAST._IExpr _out1468;
          DCOMP._IOwnership _out1469;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
          (this).GenExpr(_4162_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1468, out _out1469, out _out1470);
          _4163_recursiveGen = _out1468;
          _4164___v140 = _out1469;
          _4165_recIdents = _out1470;
          readIdents = _4165_recIdents;
          r = ((_4163_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1471;
          DCOMP._IOwnership _out1472;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1471, out _out1472);
          r = _out1471;
          resultingOwnership = _out1472;
          return ;
        }
      } else if (_source175.is_MapValues) {
        DAST._IExpression _4166___mcc_h47 = _source175.dtor_expr;
        DAST._IExpression _4167_expr = _4166___mcc_h47;
        {
          RAST._IExpr _4168_recursiveGen;
          DCOMP._IOwnership _4169___v141;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4170_recIdents;
          RAST._IExpr _out1473;
          DCOMP._IOwnership _out1474;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1475;
          (this).GenExpr(_4167_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1473, out _out1474, out _out1475);
          _4168_recursiveGen = _out1473;
          _4169___v141 = _out1474;
          _4170_recIdents = _out1475;
          readIdents = _4170_recIdents;
          r = ((_4168_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1476;
          DCOMP._IOwnership _out1477;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1476, out _out1477);
          r = _out1476;
          resultingOwnership = _out1477;
          return ;
        }
      } else if (_source175.is_Select) {
        DAST._IExpression _4171___mcc_h48 = _source175.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4172___mcc_h49 = _source175.dtor_field;
        bool _4173___mcc_h50 = _source175.dtor_isConstant;
        bool _4174___mcc_h51 = _source175.dtor_onDatatype;
        DAST._IType _4175___mcc_h52 = _source175.dtor_fieldType;
        DAST._IExpression _source178 = _4171___mcc_h48;
        if (_source178.is_Literal) {
          DAST._ILiteral _4176___mcc_h53 = _source178.dtor_Literal_i_a0;
          DAST._IType _4177_fieldType = _4175___mcc_h52;
          bool _4178_isDatatype = _4174___mcc_h51;
          bool _4179_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4180_field = _4172___mcc_h49;
          DAST._IExpression _4181_on = _4171___mcc_h48;
          {
            if (_4178_isDatatype) {
              RAST._IExpr _4182_onExpr;
              DCOMP._IOwnership _4183_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4184_recIdents;
              RAST._IExpr _out1478;
              DCOMP._IOwnership _out1479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1480;
              (this).GenExpr(_4181_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1478, out _out1479, out _out1480);
              _4182_onExpr = _out1478;
              _4183_onOwned = _out1479;
              _4184_recIdents = _out1480;
              r = ((_4182_onExpr).Sel(DCOMP.__default.escapeName(_4180_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4185_typ;
              RAST._IType _out1481;
              _out1481 = (this).GenType(_4177_fieldType, false, false);
              _4185_typ = _out1481;
              if (((_4185_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1482;
                DCOMP._IOwnership _out1483;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1482, out _out1483);
                r = _out1482;
                resultingOwnership = _out1483;
              }
              readIdents = _4184_recIdents;
            } else {
              RAST._IExpr _4186_onExpr;
              DCOMP._IOwnership _4187_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4188_recIdents;
              RAST._IExpr _out1484;
              DCOMP._IOwnership _out1485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
              (this).GenExpr(_4181_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1484, out _out1485, out _out1486);
              _4186_onExpr = _out1484;
              _4187_onOwned = _out1485;
              _4188_recIdents = _out1486;
              r = _4186_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4180_field));
              if (_4179_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4189_s;
                _4189_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4186_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4180_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4189_s);
              }
              DCOMP._IOwnership _4190_fromOwnership;
              _4190_fromOwnership = ((_4179_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1487;
              DCOMP._IOwnership _out1488;
              DCOMP.COMP.FromOwnership(r, _4190_fromOwnership, expectedOwnership, out _out1487, out _out1488);
              r = _out1487;
              resultingOwnership = _out1488;
              readIdents = _4188_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _4191___mcc_h55 = _source178.dtor_Ident_i_a0;
          DAST._IType _4192_fieldType = _4175___mcc_h52;
          bool _4193_isDatatype = _4174___mcc_h51;
          bool _4194_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4195_field = _4172___mcc_h49;
          DAST._IExpression _4196_on = _4171___mcc_h48;
          {
            if (_4193_isDatatype) {
              RAST._IExpr _4197_onExpr;
              DCOMP._IOwnership _4198_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4199_recIdents;
              RAST._IExpr _out1489;
              DCOMP._IOwnership _out1490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1491;
              (this).GenExpr(_4196_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1489, out _out1490, out _out1491);
              _4197_onExpr = _out1489;
              _4198_onOwned = _out1490;
              _4199_recIdents = _out1491;
              r = ((_4197_onExpr).Sel(DCOMP.__default.escapeName(_4195_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4200_typ;
              RAST._IType _out1492;
              _out1492 = (this).GenType(_4192_fieldType, false, false);
              _4200_typ = _out1492;
              if (((_4200_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1493;
                DCOMP._IOwnership _out1494;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1493, out _out1494);
                r = _out1493;
                resultingOwnership = _out1494;
              }
              readIdents = _4199_recIdents;
            } else {
              RAST._IExpr _4201_onExpr;
              DCOMP._IOwnership _4202_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4203_recIdents;
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1497;
              (this).GenExpr(_4196_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1495, out _out1496, out _out1497);
              _4201_onExpr = _out1495;
              _4202_onOwned = _out1496;
              _4203_recIdents = _out1497;
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
              RAST._IExpr _out1498;
              DCOMP._IOwnership _out1499;
              DCOMP.COMP.FromOwnership(r, _4205_fromOwnership, expectedOwnership, out _out1498, out _out1499);
              r = _out1498;
              resultingOwnership = _out1499;
              readIdents = _4203_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4206___mcc_h57 = _source178.dtor_Companion_i_a0;
          DAST._IType _4207_fieldType = _4175___mcc_h52;
          bool _4208_isDatatype = _4174___mcc_h51;
          bool _4209_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4210_field = _4172___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4211_c = _4206___mcc_h57;
          {
            RAST._IExpr _4212_onExpr;
            DCOMP._IOwnership _4213_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4214_recIdents;
            RAST._IExpr _out1500;
            DCOMP._IOwnership _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            (this).GenExpr(DAST.Expression.create_Companion(_4211_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1500, out _out1501, out _out1502);
            _4212_onExpr = _out1500;
            _4213_onOwned = _out1501;
            _4214_recIdents = _out1502;
            r = ((_4212_onExpr).MSel(DCOMP.__default.escapeName(_4210_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1503;
            DCOMP._IOwnership _out1504;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1503, out _out1504);
            r = _out1503;
            resultingOwnership = _out1504;
            readIdents = _4214_recIdents;
            return ;
          }
        } else if (_source178.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _4215___mcc_h59 = _source178.dtor_Tuple_i_a0;
          DAST._IType _4216_fieldType = _4175___mcc_h52;
          bool _4217_isDatatype = _4174___mcc_h51;
          bool _4218_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4219_field = _4172___mcc_h49;
          DAST._IExpression _4220_on = _4171___mcc_h48;
          {
            if (_4217_isDatatype) {
              RAST._IExpr _4221_onExpr;
              DCOMP._IOwnership _4222_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4223_recIdents;
              RAST._IExpr _out1505;
              DCOMP._IOwnership _out1506;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1507;
              (this).GenExpr(_4220_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1505, out _out1506, out _out1507);
              _4221_onExpr = _out1505;
              _4222_onOwned = _out1506;
              _4223_recIdents = _out1507;
              r = ((_4221_onExpr).Sel(DCOMP.__default.escapeName(_4219_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4224_typ;
              RAST._IType _out1508;
              _out1508 = (this).GenType(_4216_fieldType, false, false);
              _4224_typ = _out1508;
              if (((_4224_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1509;
                DCOMP._IOwnership _out1510;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
                r = _out1509;
                resultingOwnership = _out1510;
              }
              readIdents = _4223_recIdents;
            } else {
              RAST._IExpr _4225_onExpr;
              DCOMP._IOwnership _4226_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4227_recIdents;
              RAST._IExpr _out1511;
              DCOMP._IOwnership _out1512;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
              (this).GenExpr(_4220_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1511, out _out1512, out _out1513);
              _4225_onExpr = _out1511;
              _4226_onOwned = _out1512;
              _4227_recIdents = _out1513;
              r = _4225_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4219_field));
              if (_4218_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4228_s;
                _4228_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4225_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4219_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4228_s);
              }
              DCOMP._IOwnership _4229_fromOwnership;
              _4229_fromOwnership = ((_4218_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwnership(r, _4229_fromOwnership, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
              readIdents = _4227_recIdents;
            }
            return ;
          }
        } else if (_source178.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4230___mcc_h61 = _source178.dtor_path;
          Dafny.ISequence<DAST._IType> _4231___mcc_h62 = _source178.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4232___mcc_h63 = _source178.dtor_args;
          DAST._IType _4233_fieldType = _4175___mcc_h52;
          bool _4234_isDatatype = _4174___mcc_h51;
          bool _4235_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4236_field = _4172___mcc_h49;
          DAST._IExpression _4237_on = _4171___mcc_h48;
          {
            if (_4234_isDatatype) {
              RAST._IExpr _4238_onExpr;
              DCOMP._IOwnership _4239_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4240_recIdents;
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
              (this).GenExpr(_4237_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1516, out _out1517, out _out1518);
              _4238_onExpr = _out1516;
              _4239_onOwned = _out1517;
              _4240_recIdents = _out1518;
              r = ((_4238_onExpr).Sel(DCOMP.__default.escapeName(_4236_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4241_typ;
              RAST._IType _out1519;
              _out1519 = (this).GenType(_4233_fieldType, false, false);
              _4241_typ = _out1519;
              if (((_4241_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1520;
                DCOMP._IOwnership _out1521;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1520, out _out1521);
                r = _out1520;
                resultingOwnership = _out1521;
              }
              readIdents = _4240_recIdents;
            } else {
              RAST._IExpr _4242_onExpr;
              DCOMP._IOwnership _4243_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4244_recIdents;
              RAST._IExpr _out1522;
              DCOMP._IOwnership _out1523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1524;
              (this).GenExpr(_4237_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1522, out _out1523, out _out1524);
              _4242_onExpr = _out1522;
              _4243_onOwned = _out1523;
              _4244_recIdents = _out1524;
              r = _4242_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4236_field));
              if (_4235_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4245_s;
                _4245_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4242_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4236_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4245_s);
              }
              DCOMP._IOwnership _4246_fromOwnership;
              _4246_fromOwnership = ((_4235_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1525;
              DCOMP._IOwnership _out1526;
              DCOMP.COMP.FromOwnership(r, _4246_fromOwnership, expectedOwnership, out _out1525, out _out1526);
              r = _out1525;
              resultingOwnership = _out1526;
              readIdents = _4244_recIdents;
            }
            return ;
          }
        } else if (_source178.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _4247___mcc_h67 = _source178.dtor_dims;
          DAST._IType _4248___mcc_h68 = _source178.dtor_typ;
          DAST._IType _4249_fieldType = _4175___mcc_h52;
          bool _4250_isDatatype = _4174___mcc_h51;
          bool _4251_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4252_field = _4172___mcc_h49;
          DAST._IExpression _4253_on = _4171___mcc_h48;
          {
            if (_4250_isDatatype) {
              RAST._IExpr _4254_onExpr;
              DCOMP._IOwnership _4255_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4256_recIdents;
              RAST._IExpr _out1527;
              DCOMP._IOwnership _out1528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1529;
              (this).GenExpr(_4253_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1527, out _out1528, out _out1529);
              _4254_onExpr = _out1527;
              _4255_onOwned = _out1528;
              _4256_recIdents = _out1529;
              r = ((_4254_onExpr).Sel(DCOMP.__default.escapeName(_4252_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4257_typ;
              RAST._IType _out1530;
              _out1530 = (this).GenType(_4249_fieldType, false, false);
              _4257_typ = _out1530;
              if (((_4257_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1531;
                DCOMP._IOwnership _out1532;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1531, out _out1532);
                r = _out1531;
                resultingOwnership = _out1532;
              }
              readIdents = _4256_recIdents;
            } else {
              RAST._IExpr _4258_onExpr;
              DCOMP._IOwnership _4259_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4260_recIdents;
              RAST._IExpr _out1533;
              DCOMP._IOwnership _out1534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
              (this).GenExpr(_4253_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1533, out _out1534, out _out1535);
              _4258_onExpr = _out1533;
              _4259_onOwned = _out1534;
              _4260_recIdents = _out1535;
              r = _4258_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4252_field));
              if (_4251_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4261_s;
                _4261_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4258_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4252_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4261_s);
              }
              DCOMP._IOwnership _4262_fromOwnership;
              _4262_fromOwnership = ((_4251_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1536;
              DCOMP._IOwnership _out1537;
              DCOMP.COMP.FromOwnership(r, _4262_fromOwnership, expectedOwnership, out _out1536, out _out1537);
              r = _out1536;
              resultingOwnership = _out1537;
              readIdents = _4260_recIdents;
            }
            return ;
          }
        } else if (_source178.is_DatatypeValue) {
          DAST._IDatatypeType _4263___mcc_h71 = _source178.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _4264___mcc_h72 = _source178.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _4265___mcc_h73 = _source178.dtor_variant;
          bool _4266___mcc_h74 = _source178.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4267___mcc_h75 = _source178.dtor_contents;
          DAST._IType _4268_fieldType = _4175___mcc_h52;
          bool _4269_isDatatype = _4174___mcc_h51;
          bool _4270_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4271_field = _4172___mcc_h49;
          DAST._IExpression _4272_on = _4171___mcc_h48;
          {
            if (_4269_isDatatype) {
              RAST._IExpr _4273_onExpr;
              DCOMP._IOwnership _4274_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4275_recIdents;
              RAST._IExpr _out1538;
              DCOMP._IOwnership _out1539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1540;
              (this).GenExpr(_4272_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1538, out _out1539, out _out1540);
              _4273_onExpr = _out1538;
              _4274_onOwned = _out1539;
              _4275_recIdents = _out1540;
              r = ((_4273_onExpr).Sel(DCOMP.__default.escapeName(_4271_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4276_typ;
              RAST._IType _out1541;
              _out1541 = (this).GenType(_4268_fieldType, false, false);
              _4276_typ = _out1541;
              if (((_4276_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1542;
                DCOMP._IOwnership _out1543;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1542, out _out1543);
                r = _out1542;
                resultingOwnership = _out1543;
              }
              readIdents = _4275_recIdents;
            } else {
              RAST._IExpr _4277_onExpr;
              DCOMP._IOwnership _4278_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4279_recIdents;
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
              (this).GenExpr(_4272_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1544, out _out1545, out _out1546);
              _4277_onExpr = _out1544;
              _4278_onOwned = _out1545;
              _4279_recIdents = _out1546;
              r = _4277_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4271_field));
              if (_4270_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4280_s;
                _4280_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4277_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4271_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4280_s);
              }
              DCOMP._IOwnership _4281_fromOwnership;
              _4281_fromOwnership = ((_4270_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1547;
              DCOMP._IOwnership _out1548;
              DCOMP.COMP.FromOwnership(r, _4281_fromOwnership, expectedOwnership, out _out1547, out _out1548);
              r = _out1547;
              resultingOwnership = _out1548;
              readIdents = _4279_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Convert) {
          DAST._IExpression _4282___mcc_h81 = _source178.dtor_value;
          DAST._IType _4283___mcc_h82 = _source178.dtor_from;
          DAST._IType _4284___mcc_h83 = _source178.dtor_typ;
          DAST._IType _4285_fieldType = _4175___mcc_h52;
          bool _4286_isDatatype = _4174___mcc_h51;
          bool _4287_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4288_field = _4172___mcc_h49;
          DAST._IExpression _4289_on = _4171___mcc_h48;
          {
            if (_4286_isDatatype) {
              RAST._IExpr _4290_onExpr;
              DCOMP._IOwnership _4291_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4292_recIdents;
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
              (this).GenExpr(_4289_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1549, out _out1550, out _out1551);
              _4290_onExpr = _out1549;
              _4291_onOwned = _out1550;
              _4292_recIdents = _out1551;
              r = ((_4290_onExpr).Sel(DCOMP.__default.escapeName(_4288_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4293_typ;
              RAST._IType _out1552;
              _out1552 = (this).GenType(_4285_fieldType, false, false);
              _4293_typ = _out1552;
              if (((_4293_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1553;
                DCOMP._IOwnership _out1554;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1553, out _out1554);
                r = _out1553;
                resultingOwnership = _out1554;
              }
              readIdents = _4292_recIdents;
            } else {
              RAST._IExpr _4294_onExpr;
              DCOMP._IOwnership _4295_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4296_recIdents;
              RAST._IExpr _out1555;
              DCOMP._IOwnership _out1556;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1557;
              (this).GenExpr(_4289_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1555, out _out1556, out _out1557);
              _4294_onExpr = _out1555;
              _4295_onOwned = _out1556;
              _4296_recIdents = _out1557;
              r = _4294_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4288_field));
              if (_4287_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4297_s;
                _4297_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4294_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4288_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4297_s);
              }
              DCOMP._IOwnership _4298_fromOwnership;
              _4298_fromOwnership = ((_4287_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(r, _4298_fromOwnership, expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
              readIdents = _4296_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqConstruct) {
          DAST._IExpression _4299___mcc_h87 = _source178.dtor_length;
          DAST._IExpression _4300___mcc_h88 = _source178.dtor_elem;
          DAST._IType _4301_fieldType = _4175___mcc_h52;
          bool _4302_isDatatype = _4174___mcc_h51;
          bool _4303_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4304_field = _4172___mcc_h49;
          DAST._IExpression _4305_on = _4171___mcc_h48;
          {
            if (_4302_isDatatype) {
              RAST._IExpr _4306_onExpr;
              DCOMP._IOwnership _4307_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4308_recIdents;
              RAST._IExpr _out1560;
              DCOMP._IOwnership _out1561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
              (this).GenExpr(_4305_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1560, out _out1561, out _out1562);
              _4306_onExpr = _out1560;
              _4307_onOwned = _out1561;
              _4308_recIdents = _out1562;
              r = ((_4306_onExpr).Sel(DCOMP.__default.escapeName(_4304_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4309_typ;
              RAST._IType _out1563;
              _out1563 = (this).GenType(_4301_fieldType, false, false);
              _4309_typ = _out1563;
              if (((_4309_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1564;
                DCOMP._IOwnership _out1565;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1564, out _out1565);
                r = _out1564;
                resultingOwnership = _out1565;
              }
              readIdents = _4308_recIdents;
            } else {
              RAST._IExpr _4310_onExpr;
              DCOMP._IOwnership _4311_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4312_recIdents;
              RAST._IExpr _out1566;
              DCOMP._IOwnership _out1567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
              (this).GenExpr(_4305_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1566, out _out1567, out _out1568);
              _4310_onExpr = _out1566;
              _4311_onOwned = _out1567;
              _4312_recIdents = _out1568;
              r = _4310_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4304_field));
              if (_4303_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4313_s;
                _4313_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4310_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4304_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4313_s);
              }
              DCOMP._IOwnership _4314_fromOwnership;
              _4314_fromOwnership = ((_4303_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1569;
              DCOMP._IOwnership _out1570;
              DCOMP.COMP.FromOwnership(r, _4314_fromOwnership, expectedOwnership, out _out1569, out _out1570);
              r = _out1569;
              resultingOwnership = _out1570;
              readIdents = _4312_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _4315___mcc_h91 = _source178.dtor_elements;
          DAST._IType _4316___mcc_h92 = _source178.dtor_typ;
          DAST._IType _4317_fieldType = _4175___mcc_h52;
          bool _4318_isDatatype = _4174___mcc_h51;
          bool _4319_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4320_field = _4172___mcc_h49;
          DAST._IExpression _4321_on = _4171___mcc_h48;
          {
            if (_4318_isDatatype) {
              RAST._IExpr _4322_onExpr;
              DCOMP._IOwnership _4323_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4324_recIdents;
              RAST._IExpr _out1571;
              DCOMP._IOwnership _out1572;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1573;
              (this).GenExpr(_4321_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1571, out _out1572, out _out1573);
              _4322_onExpr = _out1571;
              _4323_onOwned = _out1572;
              _4324_recIdents = _out1573;
              r = ((_4322_onExpr).Sel(DCOMP.__default.escapeName(_4320_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4325_typ;
              RAST._IType _out1574;
              _out1574 = (this).GenType(_4317_fieldType, false, false);
              _4325_typ = _out1574;
              if (((_4325_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1575;
                DCOMP._IOwnership _out1576;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1575, out _out1576);
                r = _out1575;
                resultingOwnership = _out1576;
              }
              readIdents = _4324_recIdents;
            } else {
              RAST._IExpr _4326_onExpr;
              DCOMP._IOwnership _4327_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4328_recIdents;
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1579;
              (this).GenExpr(_4321_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1577, out _out1578, out _out1579);
              _4326_onExpr = _out1577;
              _4327_onOwned = _out1578;
              _4328_recIdents = _out1579;
              r = _4326_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4320_field));
              if (_4319_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4329_s;
                _4329_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4326_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4320_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4329_s);
              }
              DCOMP._IOwnership _4330_fromOwnership;
              _4330_fromOwnership = ((_4319_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1580;
              DCOMP._IOwnership _out1581;
              DCOMP.COMP.FromOwnership(r, _4330_fromOwnership, expectedOwnership, out _out1580, out _out1581);
              r = _out1580;
              resultingOwnership = _out1581;
              readIdents = _4328_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _4331___mcc_h95 = _source178.dtor_elements;
          DAST._IType _4332_fieldType = _4175___mcc_h52;
          bool _4333_isDatatype = _4174___mcc_h51;
          bool _4334_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4335_field = _4172___mcc_h49;
          DAST._IExpression _4336_on = _4171___mcc_h48;
          {
            if (_4333_isDatatype) {
              RAST._IExpr _4337_onExpr;
              DCOMP._IOwnership _4338_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4339_recIdents;
              RAST._IExpr _out1582;
              DCOMP._IOwnership _out1583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1584;
              (this).GenExpr(_4336_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1582, out _out1583, out _out1584);
              _4337_onExpr = _out1582;
              _4338_onOwned = _out1583;
              _4339_recIdents = _out1584;
              r = ((_4337_onExpr).Sel(DCOMP.__default.escapeName(_4335_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4340_typ;
              RAST._IType _out1585;
              _out1585 = (this).GenType(_4332_fieldType, false, false);
              _4340_typ = _out1585;
              if (((_4340_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1586;
                DCOMP._IOwnership _out1587;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
                r = _out1586;
                resultingOwnership = _out1587;
              }
              readIdents = _4339_recIdents;
            } else {
              RAST._IExpr _4341_onExpr;
              DCOMP._IOwnership _4342_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4343_recIdents;
              RAST._IExpr _out1588;
              DCOMP._IOwnership _out1589;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
              (this).GenExpr(_4336_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1588, out _out1589, out _out1590);
              _4341_onExpr = _out1588;
              _4342_onOwned = _out1589;
              _4343_recIdents = _out1590;
              r = _4341_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4335_field));
              if (_4334_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4344_s;
                _4344_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4341_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4335_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4344_s);
              }
              DCOMP._IOwnership _4345_fromOwnership;
              _4345_fromOwnership = ((_4334_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwnership(r, _4345_fromOwnership, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
              readIdents = _4343_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _4346___mcc_h97 = _source178.dtor_elements;
          DAST._IType _4347_fieldType = _4175___mcc_h52;
          bool _4348_isDatatype = _4174___mcc_h51;
          bool _4349_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4350_field = _4172___mcc_h49;
          DAST._IExpression _4351_on = _4171___mcc_h48;
          {
            if (_4348_isDatatype) {
              RAST._IExpr _4352_onExpr;
              DCOMP._IOwnership _4353_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4354_recIdents;
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1595;
              (this).GenExpr(_4351_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1593, out _out1594, out _out1595);
              _4352_onExpr = _out1593;
              _4353_onOwned = _out1594;
              _4354_recIdents = _out1595;
              r = ((_4352_onExpr).Sel(DCOMP.__default.escapeName(_4350_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4355_typ;
              RAST._IType _out1596;
              _out1596 = (this).GenType(_4347_fieldType, false, false);
              _4355_typ = _out1596;
              if (((_4355_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1597;
                DCOMP._IOwnership _out1598;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1597, out _out1598);
                r = _out1597;
                resultingOwnership = _out1598;
              }
              readIdents = _4354_recIdents;
            } else {
              RAST._IExpr _4356_onExpr;
              DCOMP._IOwnership _4357_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4358_recIdents;
              RAST._IExpr _out1599;
              DCOMP._IOwnership _out1600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1601;
              (this).GenExpr(_4351_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1599, out _out1600, out _out1601);
              _4356_onExpr = _out1599;
              _4357_onOwned = _out1600;
              _4358_recIdents = _out1601;
              r = _4356_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4350_field));
              if (_4349_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4359_s;
                _4359_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4356_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4350_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4359_s);
              }
              DCOMP._IOwnership _4360_fromOwnership;
              _4360_fromOwnership = ((_4349_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1602;
              DCOMP._IOwnership _out1603;
              DCOMP.COMP.FromOwnership(r, _4360_fromOwnership, expectedOwnership, out _out1602, out _out1603);
              r = _out1602;
              resultingOwnership = _out1603;
              readIdents = _4358_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4361___mcc_h99 = _source178.dtor_mapElems;
          DAST._IType _4362_fieldType = _4175___mcc_h52;
          bool _4363_isDatatype = _4174___mcc_h51;
          bool _4364_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4365_field = _4172___mcc_h49;
          DAST._IExpression _4366_on = _4171___mcc_h48;
          {
            if (_4363_isDatatype) {
              RAST._IExpr _4367_onExpr;
              DCOMP._IOwnership _4368_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4369_recIdents;
              RAST._IExpr _out1604;
              DCOMP._IOwnership _out1605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1606;
              (this).GenExpr(_4366_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1604, out _out1605, out _out1606);
              _4367_onExpr = _out1604;
              _4368_onOwned = _out1605;
              _4369_recIdents = _out1606;
              r = ((_4367_onExpr).Sel(DCOMP.__default.escapeName(_4365_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4370_typ;
              RAST._IType _out1607;
              _out1607 = (this).GenType(_4362_fieldType, false, false);
              _4370_typ = _out1607;
              if (((_4370_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1608;
                DCOMP._IOwnership _out1609;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1608, out _out1609);
                r = _out1608;
                resultingOwnership = _out1609;
              }
              readIdents = _4369_recIdents;
            } else {
              RAST._IExpr _4371_onExpr;
              DCOMP._IOwnership _4372_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4373_recIdents;
              RAST._IExpr _out1610;
              DCOMP._IOwnership _out1611;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1612;
              (this).GenExpr(_4366_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1610, out _out1611, out _out1612);
              _4371_onExpr = _out1610;
              _4372_onOwned = _out1611;
              _4373_recIdents = _out1612;
              r = _4371_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4365_field));
              if (_4364_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4374_s;
                _4374_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4371_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4365_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4374_s);
              }
              DCOMP._IOwnership _4375_fromOwnership;
              _4375_fromOwnership = ((_4364_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1613;
              DCOMP._IOwnership _out1614;
              DCOMP.COMP.FromOwnership(r, _4375_fromOwnership, expectedOwnership, out _out1613, out _out1614);
              r = _out1613;
              resultingOwnership = _out1614;
              readIdents = _4373_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapBuilder) {
          DAST._IType _4376___mcc_h101 = _source178.dtor_keyType;
          DAST._IType _4377___mcc_h102 = _source178.dtor_valueType;
          DAST._IType _4378_fieldType = _4175___mcc_h52;
          bool _4379_isDatatype = _4174___mcc_h51;
          bool _4380_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4381_field = _4172___mcc_h49;
          DAST._IExpression _4382_on = _4171___mcc_h48;
          {
            if (_4379_isDatatype) {
              RAST._IExpr _4383_onExpr;
              DCOMP._IOwnership _4384_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4385_recIdents;
              RAST._IExpr _out1615;
              DCOMP._IOwnership _out1616;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1617;
              (this).GenExpr(_4382_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1615, out _out1616, out _out1617);
              _4383_onExpr = _out1615;
              _4384_onOwned = _out1616;
              _4385_recIdents = _out1617;
              r = ((_4383_onExpr).Sel(DCOMP.__default.escapeName(_4381_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4386_typ;
              RAST._IType _out1618;
              _out1618 = (this).GenType(_4378_fieldType, false, false);
              _4386_typ = _out1618;
              if (((_4386_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1619;
                DCOMP._IOwnership _out1620;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1619, out _out1620);
                r = _out1619;
                resultingOwnership = _out1620;
              }
              readIdents = _4385_recIdents;
            } else {
              RAST._IExpr _4387_onExpr;
              DCOMP._IOwnership _4388_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4389_recIdents;
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1623;
              (this).GenExpr(_4382_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1621, out _out1622, out _out1623);
              _4387_onExpr = _out1621;
              _4388_onOwned = _out1622;
              _4389_recIdents = _out1623;
              r = _4387_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4381_field));
              if (_4380_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4390_s;
                _4390_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4387_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4381_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4390_s);
              }
              DCOMP._IOwnership _4391_fromOwnership;
              _4391_fromOwnership = ((_4380_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1624;
              DCOMP._IOwnership _out1625;
              DCOMP.COMP.FromOwnership(r, _4391_fromOwnership, expectedOwnership, out _out1624, out _out1625);
              r = _out1624;
              resultingOwnership = _out1625;
              readIdents = _4389_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqUpdate) {
          DAST._IExpression _4392___mcc_h105 = _source178.dtor_expr;
          DAST._IExpression _4393___mcc_h106 = _source178.dtor_indexExpr;
          DAST._IExpression _4394___mcc_h107 = _source178.dtor_value;
          DAST._IType _4395_fieldType = _4175___mcc_h52;
          bool _4396_isDatatype = _4174___mcc_h51;
          bool _4397_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4398_field = _4172___mcc_h49;
          DAST._IExpression _4399_on = _4171___mcc_h48;
          {
            if (_4396_isDatatype) {
              RAST._IExpr _4400_onExpr;
              DCOMP._IOwnership _4401_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4402_recIdents;
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1628;
              (this).GenExpr(_4399_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1626, out _out1627, out _out1628);
              _4400_onExpr = _out1626;
              _4401_onOwned = _out1627;
              _4402_recIdents = _out1628;
              r = ((_4400_onExpr).Sel(DCOMP.__default.escapeName(_4398_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4403_typ;
              RAST._IType _out1629;
              _out1629 = (this).GenType(_4395_fieldType, false, false);
              _4403_typ = _out1629;
              if (((_4403_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1630;
                DCOMP._IOwnership _out1631;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1630, out _out1631);
                r = _out1630;
                resultingOwnership = _out1631;
              }
              readIdents = _4402_recIdents;
            } else {
              RAST._IExpr _4404_onExpr;
              DCOMP._IOwnership _4405_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4406_recIdents;
              RAST._IExpr _out1632;
              DCOMP._IOwnership _out1633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1634;
              (this).GenExpr(_4399_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1632, out _out1633, out _out1634);
              _4404_onExpr = _out1632;
              _4405_onOwned = _out1633;
              _4406_recIdents = _out1634;
              r = _4404_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4398_field));
              if (_4397_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4407_s;
                _4407_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4404_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4398_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4407_s);
              }
              DCOMP._IOwnership _4408_fromOwnership;
              _4408_fromOwnership = ((_4397_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(r, _4408_fromOwnership, expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
              readIdents = _4406_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapUpdate) {
          DAST._IExpression _4409___mcc_h111 = _source178.dtor_expr;
          DAST._IExpression _4410___mcc_h112 = _source178.dtor_indexExpr;
          DAST._IExpression _4411___mcc_h113 = _source178.dtor_value;
          DAST._IType _4412_fieldType = _4175___mcc_h52;
          bool _4413_isDatatype = _4174___mcc_h51;
          bool _4414_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4415_field = _4172___mcc_h49;
          DAST._IExpression _4416_on = _4171___mcc_h48;
          {
            if (_4413_isDatatype) {
              RAST._IExpr _4417_onExpr;
              DCOMP._IOwnership _4418_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4419_recIdents;
              RAST._IExpr _out1637;
              DCOMP._IOwnership _out1638;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
              (this).GenExpr(_4416_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1637, out _out1638, out _out1639);
              _4417_onExpr = _out1637;
              _4418_onOwned = _out1638;
              _4419_recIdents = _out1639;
              r = ((_4417_onExpr).Sel(DCOMP.__default.escapeName(_4415_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4420_typ;
              RAST._IType _out1640;
              _out1640 = (this).GenType(_4412_fieldType, false, false);
              _4420_typ = _out1640;
              if (((_4420_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1641;
                DCOMP._IOwnership _out1642;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1641, out _out1642);
                r = _out1641;
                resultingOwnership = _out1642;
              }
              readIdents = _4419_recIdents;
            } else {
              RAST._IExpr _4421_onExpr;
              DCOMP._IOwnership _4422_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4423_recIdents;
              RAST._IExpr _out1643;
              DCOMP._IOwnership _out1644;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1645;
              (this).GenExpr(_4416_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1643, out _out1644, out _out1645);
              _4421_onExpr = _out1643;
              _4422_onOwned = _out1644;
              _4423_recIdents = _out1645;
              r = _4421_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4415_field));
              if (_4414_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4424_s;
                _4424_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4421_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4415_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4424_s);
              }
              DCOMP._IOwnership _4425_fromOwnership;
              _4425_fromOwnership = ((_4414_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1646;
              DCOMP._IOwnership _out1647;
              DCOMP.COMP.FromOwnership(r, _4425_fromOwnership, expectedOwnership, out _out1646, out _out1647);
              r = _out1646;
              resultingOwnership = _out1647;
              readIdents = _4423_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetBuilder) {
          DAST._IType _4426___mcc_h117 = _source178.dtor_elemType;
          DAST._IType _4427_fieldType = _4175___mcc_h52;
          bool _4428_isDatatype = _4174___mcc_h51;
          bool _4429_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4430_field = _4172___mcc_h49;
          DAST._IExpression _4431_on = _4171___mcc_h48;
          {
            if (_4428_isDatatype) {
              RAST._IExpr _4432_onExpr;
              DCOMP._IOwnership _4433_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4434_recIdents;
              RAST._IExpr _out1648;
              DCOMP._IOwnership _out1649;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1650;
              (this).GenExpr(_4431_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1648, out _out1649, out _out1650);
              _4432_onExpr = _out1648;
              _4433_onOwned = _out1649;
              _4434_recIdents = _out1650;
              r = ((_4432_onExpr).Sel(DCOMP.__default.escapeName(_4430_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4435_typ;
              RAST._IType _out1651;
              _out1651 = (this).GenType(_4427_fieldType, false, false);
              _4435_typ = _out1651;
              if (((_4435_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1652;
                DCOMP._IOwnership _out1653;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1652, out _out1653);
                r = _out1652;
                resultingOwnership = _out1653;
              }
              readIdents = _4434_recIdents;
            } else {
              RAST._IExpr _4436_onExpr;
              DCOMP._IOwnership _4437_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4438_recIdents;
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1656;
              (this).GenExpr(_4431_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1654, out _out1655, out _out1656);
              _4436_onExpr = _out1654;
              _4437_onOwned = _out1655;
              _4438_recIdents = _out1656;
              r = _4436_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4430_field));
              if (_4429_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4439_s;
                _4439_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4436_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4430_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4439_s);
              }
              DCOMP._IOwnership _4440_fromOwnership;
              _4440_fromOwnership = ((_4429_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1657;
              DCOMP._IOwnership _out1658;
              DCOMP.COMP.FromOwnership(r, _4440_fromOwnership, expectedOwnership, out _out1657, out _out1658);
              r = _out1657;
              resultingOwnership = _out1658;
              readIdents = _4438_recIdents;
            }
            return ;
          }
        } else if (_source178.is_ToMultiset) {
          DAST._IExpression _4441___mcc_h119 = _source178.dtor_ToMultiset_i_a0;
          DAST._IType _4442_fieldType = _4175___mcc_h52;
          bool _4443_isDatatype = _4174___mcc_h51;
          bool _4444_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4445_field = _4172___mcc_h49;
          DAST._IExpression _4446_on = _4171___mcc_h48;
          {
            if (_4443_isDatatype) {
              RAST._IExpr _4447_onExpr;
              DCOMP._IOwnership _4448_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4449_recIdents;
              RAST._IExpr _out1659;
              DCOMP._IOwnership _out1660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1661;
              (this).GenExpr(_4446_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1659, out _out1660, out _out1661);
              _4447_onExpr = _out1659;
              _4448_onOwned = _out1660;
              _4449_recIdents = _out1661;
              r = ((_4447_onExpr).Sel(DCOMP.__default.escapeName(_4445_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4450_typ;
              RAST._IType _out1662;
              _out1662 = (this).GenType(_4442_fieldType, false, false);
              _4450_typ = _out1662;
              if (((_4450_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1663;
                DCOMP._IOwnership _out1664;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
                r = _out1663;
                resultingOwnership = _out1664;
              }
              readIdents = _4449_recIdents;
            } else {
              RAST._IExpr _4451_onExpr;
              DCOMP._IOwnership _4452_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4453_recIdents;
              RAST._IExpr _out1665;
              DCOMP._IOwnership _out1666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
              (this).GenExpr(_4446_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1665, out _out1666, out _out1667);
              _4451_onExpr = _out1665;
              _4452_onOwned = _out1666;
              _4453_recIdents = _out1667;
              r = _4451_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4445_field));
              if (_4444_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4454_s;
                _4454_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4451_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4445_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4454_s);
              }
              DCOMP._IOwnership _4455_fromOwnership;
              _4455_fromOwnership = ((_4444_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwnership(r, _4455_fromOwnership, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
              readIdents = _4453_recIdents;
            }
            return ;
          }
        } else if (_source178.is_This) {
          DAST._IType _4456_fieldType = _4175___mcc_h52;
          bool _4457_isDatatype = _4174___mcc_h51;
          bool _4458_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4459_field = _4172___mcc_h49;
          DAST._IExpression _4460_on = _4171___mcc_h48;
          {
            if (_4457_isDatatype) {
              RAST._IExpr _4461_onExpr;
              DCOMP._IOwnership _4462_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4463_recIdents;
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1672;
              (this).GenExpr(_4460_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1670, out _out1671, out _out1672);
              _4461_onExpr = _out1670;
              _4462_onOwned = _out1671;
              _4463_recIdents = _out1672;
              r = ((_4461_onExpr).Sel(DCOMP.__default.escapeName(_4459_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4464_typ;
              RAST._IType _out1673;
              _out1673 = (this).GenType(_4456_fieldType, false, false);
              _4464_typ = _out1673;
              if (((_4464_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1674;
                DCOMP._IOwnership _out1675;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1674, out _out1675);
                r = _out1674;
                resultingOwnership = _out1675;
              }
              readIdents = _4463_recIdents;
            } else {
              RAST._IExpr _4465_onExpr;
              DCOMP._IOwnership _4466_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4467_recIdents;
              RAST._IExpr _out1676;
              DCOMP._IOwnership _out1677;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1678;
              (this).GenExpr(_4460_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1676, out _out1677, out _out1678);
              _4465_onExpr = _out1676;
              _4466_onOwned = _out1677;
              _4467_recIdents = _out1678;
              r = _4465_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4459_field));
              if (_4458_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4468_s;
                _4468_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4465_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4459_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4468_s);
              }
              DCOMP._IOwnership _4469_fromOwnership;
              _4469_fromOwnership = ((_4458_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1679;
              DCOMP._IOwnership _out1680;
              DCOMP.COMP.FromOwnership(r, _4469_fromOwnership, expectedOwnership, out _out1679, out _out1680);
              r = _out1679;
              resultingOwnership = _out1680;
              readIdents = _4467_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Ite) {
          DAST._IExpression _4470___mcc_h121 = _source178.dtor_cond;
          DAST._IExpression _4471___mcc_h122 = _source178.dtor_thn;
          DAST._IExpression _4472___mcc_h123 = _source178.dtor_els;
          DAST._IType _4473_fieldType = _4175___mcc_h52;
          bool _4474_isDatatype = _4174___mcc_h51;
          bool _4475_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4476_field = _4172___mcc_h49;
          DAST._IExpression _4477_on = _4171___mcc_h48;
          {
            if (_4474_isDatatype) {
              RAST._IExpr _4478_onExpr;
              DCOMP._IOwnership _4479_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4480_recIdents;
              RAST._IExpr _out1681;
              DCOMP._IOwnership _out1682;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1683;
              (this).GenExpr(_4477_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1681, out _out1682, out _out1683);
              _4478_onExpr = _out1681;
              _4479_onOwned = _out1682;
              _4480_recIdents = _out1683;
              r = ((_4478_onExpr).Sel(DCOMP.__default.escapeName(_4476_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4481_typ;
              RAST._IType _out1684;
              _out1684 = (this).GenType(_4473_fieldType, false, false);
              _4481_typ = _out1684;
              if (((_4481_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1685;
                DCOMP._IOwnership _out1686;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1685, out _out1686);
                r = _out1685;
                resultingOwnership = _out1686;
              }
              readIdents = _4480_recIdents;
            } else {
              RAST._IExpr _4482_onExpr;
              DCOMP._IOwnership _4483_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4484_recIdents;
              RAST._IExpr _out1687;
              DCOMP._IOwnership _out1688;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1689;
              (this).GenExpr(_4477_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1687, out _out1688, out _out1689);
              _4482_onExpr = _out1687;
              _4483_onOwned = _out1688;
              _4484_recIdents = _out1689;
              r = _4482_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4476_field));
              if (_4475_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4485_s;
                _4485_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4482_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4476_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4485_s);
              }
              DCOMP._IOwnership _4486_fromOwnership;
              _4486_fromOwnership = ((_4475_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1690;
              DCOMP._IOwnership _out1691;
              DCOMP.COMP.FromOwnership(r, _4486_fromOwnership, expectedOwnership, out _out1690, out _out1691);
              r = _out1690;
              resultingOwnership = _out1691;
              readIdents = _4484_recIdents;
            }
            return ;
          }
        } else if (_source178.is_UnOp) {
          DAST._IUnaryOp _4487___mcc_h127 = _source178.dtor_unOp;
          DAST._IExpression _4488___mcc_h128 = _source178.dtor_expr;
          DAST.Format._IUnaryOpFormat _4489___mcc_h129 = _source178.dtor_format1;
          DAST._IType _4490_fieldType = _4175___mcc_h52;
          bool _4491_isDatatype = _4174___mcc_h51;
          bool _4492_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4493_field = _4172___mcc_h49;
          DAST._IExpression _4494_on = _4171___mcc_h48;
          {
            if (_4491_isDatatype) {
              RAST._IExpr _4495_onExpr;
              DCOMP._IOwnership _4496_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4497_recIdents;
              RAST._IExpr _out1692;
              DCOMP._IOwnership _out1693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1694;
              (this).GenExpr(_4494_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1692, out _out1693, out _out1694);
              _4495_onExpr = _out1692;
              _4496_onOwned = _out1693;
              _4497_recIdents = _out1694;
              r = ((_4495_onExpr).Sel(DCOMP.__default.escapeName(_4493_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4498_typ;
              RAST._IType _out1695;
              _out1695 = (this).GenType(_4490_fieldType, false, false);
              _4498_typ = _out1695;
              if (((_4498_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1696;
                DCOMP._IOwnership _out1697;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1696, out _out1697);
                r = _out1696;
                resultingOwnership = _out1697;
              }
              readIdents = _4497_recIdents;
            } else {
              RAST._IExpr _4499_onExpr;
              DCOMP._IOwnership _4500_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4501_recIdents;
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1700;
              (this).GenExpr(_4494_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1698, out _out1699, out _out1700);
              _4499_onExpr = _out1698;
              _4500_onOwned = _out1699;
              _4501_recIdents = _out1700;
              r = _4499_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4493_field));
              if (_4492_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4502_s;
                _4502_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4499_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4493_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4502_s);
              }
              DCOMP._IOwnership _4503_fromOwnership;
              _4503_fromOwnership = ((_4492_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1701;
              DCOMP._IOwnership _out1702;
              DCOMP.COMP.FromOwnership(r, _4503_fromOwnership, expectedOwnership, out _out1701, out _out1702);
              r = _out1701;
              resultingOwnership = _out1702;
              readIdents = _4501_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BinOp) {
          DAST._IBinOp _4504___mcc_h133 = _source178.dtor_op;
          DAST._IExpression _4505___mcc_h134 = _source178.dtor_left;
          DAST._IExpression _4506___mcc_h135 = _source178.dtor_right;
          DAST.Format._IBinaryOpFormat _4507___mcc_h136 = _source178.dtor_format2;
          DAST._IType _4508_fieldType = _4175___mcc_h52;
          bool _4509_isDatatype = _4174___mcc_h51;
          bool _4510_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4511_field = _4172___mcc_h49;
          DAST._IExpression _4512_on = _4171___mcc_h48;
          {
            if (_4509_isDatatype) {
              RAST._IExpr _4513_onExpr;
              DCOMP._IOwnership _4514_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4515_recIdents;
              RAST._IExpr _out1703;
              DCOMP._IOwnership _out1704;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1705;
              (this).GenExpr(_4512_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1703, out _out1704, out _out1705);
              _4513_onExpr = _out1703;
              _4514_onOwned = _out1704;
              _4515_recIdents = _out1705;
              r = ((_4513_onExpr).Sel(DCOMP.__default.escapeName(_4511_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4516_typ;
              RAST._IType _out1706;
              _out1706 = (this).GenType(_4508_fieldType, false, false);
              _4516_typ = _out1706;
              if (((_4516_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1707;
                DCOMP._IOwnership _out1708;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1707, out _out1708);
                r = _out1707;
                resultingOwnership = _out1708;
              }
              readIdents = _4515_recIdents;
            } else {
              RAST._IExpr _4517_onExpr;
              DCOMP._IOwnership _4518_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4519_recIdents;
              RAST._IExpr _out1709;
              DCOMP._IOwnership _out1710;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1711;
              (this).GenExpr(_4512_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1709, out _out1710, out _out1711);
              _4517_onExpr = _out1709;
              _4518_onOwned = _out1710;
              _4519_recIdents = _out1711;
              r = _4517_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4511_field));
              if (_4510_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4520_s;
                _4520_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4517_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4511_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4520_s);
              }
              DCOMP._IOwnership _4521_fromOwnership;
              _4521_fromOwnership = ((_4510_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1712;
              DCOMP._IOwnership _out1713;
              DCOMP.COMP.FromOwnership(r, _4521_fromOwnership, expectedOwnership, out _out1712, out _out1713);
              r = _out1712;
              resultingOwnership = _out1713;
              readIdents = _4519_recIdents;
            }
            return ;
          }
        } else if (_source178.is_ArrayLen) {
          DAST._IExpression _4522___mcc_h141 = _source178.dtor_expr;
          BigInteger _4523___mcc_h142 = _source178.dtor_dim;
          DAST._IType _4524_fieldType = _4175___mcc_h52;
          bool _4525_isDatatype = _4174___mcc_h51;
          bool _4526_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4527_field = _4172___mcc_h49;
          DAST._IExpression _4528_on = _4171___mcc_h48;
          {
            if (_4525_isDatatype) {
              RAST._IExpr _4529_onExpr;
              DCOMP._IOwnership _4530_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4531_recIdents;
              RAST._IExpr _out1714;
              DCOMP._IOwnership _out1715;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1716;
              (this).GenExpr(_4528_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1714, out _out1715, out _out1716);
              _4529_onExpr = _out1714;
              _4530_onOwned = _out1715;
              _4531_recIdents = _out1716;
              r = ((_4529_onExpr).Sel(DCOMP.__default.escapeName(_4527_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4532_typ;
              RAST._IType _out1717;
              _out1717 = (this).GenType(_4524_fieldType, false, false);
              _4532_typ = _out1717;
              if (((_4532_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1718;
                DCOMP._IOwnership _out1719;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1718, out _out1719);
                r = _out1718;
                resultingOwnership = _out1719;
              }
              readIdents = _4531_recIdents;
            } else {
              RAST._IExpr _4533_onExpr;
              DCOMP._IOwnership _4534_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4535_recIdents;
              RAST._IExpr _out1720;
              DCOMP._IOwnership _out1721;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1722;
              (this).GenExpr(_4528_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1720, out _out1721, out _out1722);
              _4533_onExpr = _out1720;
              _4534_onOwned = _out1721;
              _4535_recIdents = _out1722;
              r = _4533_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4527_field));
              if (_4526_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4536_s;
                _4536_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4533_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4527_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4536_s);
              }
              DCOMP._IOwnership _4537_fromOwnership;
              _4537_fromOwnership = ((_4526_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1723;
              DCOMP._IOwnership _out1724;
              DCOMP.COMP.FromOwnership(r, _4537_fromOwnership, expectedOwnership, out _out1723, out _out1724);
              r = _out1723;
              resultingOwnership = _out1724;
              readIdents = _4535_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapKeys) {
          DAST._IExpression _4538___mcc_h145 = _source178.dtor_expr;
          DAST._IType _4539_fieldType = _4175___mcc_h52;
          bool _4540_isDatatype = _4174___mcc_h51;
          bool _4541_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4542_field = _4172___mcc_h49;
          DAST._IExpression _4543_on = _4171___mcc_h48;
          {
            if (_4540_isDatatype) {
              RAST._IExpr _4544_onExpr;
              DCOMP._IOwnership _4545_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4546_recIdents;
              RAST._IExpr _out1725;
              DCOMP._IOwnership _out1726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1727;
              (this).GenExpr(_4543_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1725, out _out1726, out _out1727);
              _4544_onExpr = _out1725;
              _4545_onOwned = _out1726;
              _4546_recIdents = _out1727;
              r = ((_4544_onExpr).Sel(DCOMP.__default.escapeName(_4542_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4547_typ;
              RAST._IType _out1728;
              _out1728 = (this).GenType(_4539_fieldType, false, false);
              _4547_typ = _out1728;
              if (((_4547_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1729;
                DCOMP._IOwnership _out1730;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1729, out _out1730);
                r = _out1729;
                resultingOwnership = _out1730;
              }
              readIdents = _4546_recIdents;
            } else {
              RAST._IExpr _4548_onExpr;
              DCOMP._IOwnership _4549_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4550_recIdents;
              RAST._IExpr _out1731;
              DCOMP._IOwnership _out1732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1733;
              (this).GenExpr(_4543_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1731, out _out1732, out _out1733);
              _4548_onExpr = _out1731;
              _4549_onOwned = _out1732;
              _4550_recIdents = _out1733;
              r = _4548_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4542_field));
              if (_4541_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4551_s;
                _4551_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4548_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4542_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4551_s);
              }
              DCOMP._IOwnership _4552_fromOwnership;
              _4552_fromOwnership = ((_4541_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1734;
              DCOMP._IOwnership _out1735;
              DCOMP.COMP.FromOwnership(r, _4552_fromOwnership, expectedOwnership, out _out1734, out _out1735);
              r = _out1734;
              resultingOwnership = _out1735;
              readIdents = _4550_recIdents;
            }
            return ;
          }
        } else if (_source178.is_MapValues) {
          DAST._IExpression _4553___mcc_h147 = _source178.dtor_expr;
          DAST._IType _4554_fieldType = _4175___mcc_h52;
          bool _4555_isDatatype = _4174___mcc_h51;
          bool _4556_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4557_field = _4172___mcc_h49;
          DAST._IExpression _4558_on = _4171___mcc_h48;
          {
            if (_4555_isDatatype) {
              RAST._IExpr _4559_onExpr;
              DCOMP._IOwnership _4560_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4561_recIdents;
              RAST._IExpr _out1736;
              DCOMP._IOwnership _out1737;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1738;
              (this).GenExpr(_4558_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1736, out _out1737, out _out1738);
              _4559_onExpr = _out1736;
              _4560_onOwned = _out1737;
              _4561_recIdents = _out1738;
              r = ((_4559_onExpr).Sel(DCOMP.__default.escapeName(_4557_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4562_typ;
              RAST._IType _out1739;
              _out1739 = (this).GenType(_4554_fieldType, false, false);
              _4562_typ = _out1739;
              if (((_4562_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1740;
                DCOMP._IOwnership _out1741;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1740, out _out1741);
                r = _out1740;
                resultingOwnership = _out1741;
              }
              readIdents = _4561_recIdents;
            } else {
              RAST._IExpr _4563_onExpr;
              DCOMP._IOwnership _4564_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4565_recIdents;
              RAST._IExpr _out1742;
              DCOMP._IOwnership _out1743;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1744;
              (this).GenExpr(_4558_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1742, out _out1743, out _out1744);
              _4563_onExpr = _out1742;
              _4564_onOwned = _out1743;
              _4565_recIdents = _out1744;
              r = _4563_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4557_field));
              if (_4556_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4566_s;
                _4566_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4563_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4557_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4566_s);
              }
              DCOMP._IOwnership _4567_fromOwnership;
              _4567_fromOwnership = ((_4556_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1745;
              DCOMP._IOwnership _out1746;
              DCOMP.COMP.FromOwnership(r, _4567_fromOwnership, expectedOwnership, out _out1745, out _out1746);
              r = _out1745;
              resultingOwnership = _out1746;
              readIdents = _4565_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Select) {
          DAST._IExpression _4568___mcc_h149 = _source178.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4569___mcc_h150 = _source178.dtor_field;
          bool _4570___mcc_h151 = _source178.dtor_isConstant;
          bool _4571___mcc_h152 = _source178.dtor_onDatatype;
          DAST._IType _4572___mcc_h153 = _source178.dtor_fieldType;
          DAST._IType _4573_fieldType = _4175___mcc_h52;
          bool _4574_isDatatype = _4174___mcc_h51;
          bool _4575_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4576_field = _4172___mcc_h49;
          DAST._IExpression _4577_on = _4171___mcc_h48;
          {
            if (_4574_isDatatype) {
              RAST._IExpr _4578_onExpr;
              DCOMP._IOwnership _4579_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4580_recIdents;
              RAST._IExpr _out1747;
              DCOMP._IOwnership _out1748;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1749;
              (this).GenExpr(_4577_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1747, out _out1748, out _out1749);
              _4578_onExpr = _out1747;
              _4579_onOwned = _out1748;
              _4580_recIdents = _out1749;
              r = ((_4578_onExpr).Sel(DCOMP.__default.escapeName(_4576_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4581_typ;
              RAST._IType _out1750;
              _out1750 = (this).GenType(_4573_fieldType, false, false);
              _4581_typ = _out1750;
              if (((_4581_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1751;
                DCOMP._IOwnership _out1752;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1751, out _out1752);
                r = _out1751;
                resultingOwnership = _out1752;
              }
              readIdents = _4580_recIdents;
            } else {
              RAST._IExpr _4582_onExpr;
              DCOMP._IOwnership _4583_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4584_recIdents;
              RAST._IExpr _out1753;
              DCOMP._IOwnership _out1754;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
              (this).GenExpr(_4577_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1753, out _out1754, out _out1755);
              _4582_onExpr = _out1753;
              _4583_onOwned = _out1754;
              _4584_recIdents = _out1755;
              r = _4582_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4576_field));
              if (_4575_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4585_s;
                _4585_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4582_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4576_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4585_s);
              }
              DCOMP._IOwnership _4586_fromOwnership;
              _4586_fromOwnership = ((_4575_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1756;
              DCOMP._IOwnership _out1757;
              DCOMP.COMP.FromOwnership(r, _4586_fromOwnership, expectedOwnership, out _out1756, out _out1757);
              r = _out1756;
              resultingOwnership = _out1757;
              readIdents = _4584_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SelectFn) {
          DAST._IExpression _4587___mcc_h159 = _source178.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4588___mcc_h160 = _source178.dtor_field;
          bool _4589___mcc_h161 = _source178.dtor_onDatatype;
          bool _4590___mcc_h162 = _source178.dtor_isStatic;
          BigInteger _4591___mcc_h163 = _source178.dtor_arity;
          DAST._IType _4592_fieldType = _4175___mcc_h52;
          bool _4593_isDatatype = _4174___mcc_h51;
          bool _4594_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4595_field = _4172___mcc_h49;
          DAST._IExpression _4596_on = _4171___mcc_h48;
          {
            if (_4593_isDatatype) {
              RAST._IExpr _4597_onExpr;
              DCOMP._IOwnership _4598_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4599_recIdents;
              RAST._IExpr _out1758;
              DCOMP._IOwnership _out1759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1760;
              (this).GenExpr(_4596_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1758, out _out1759, out _out1760);
              _4597_onExpr = _out1758;
              _4598_onOwned = _out1759;
              _4599_recIdents = _out1760;
              r = ((_4597_onExpr).Sel(DCOMP.__default.escapeName(_4595_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4600_typ;
              RAST._IType _out1761;
              _out1761 = (this).GenType(_4592_fieldType, false, false);
              _4600_typ = _out1761;
              if (((_4600_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1762;
                DCOMP._IOwnership _out1763;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1762, out _out1763);
                r = _out1762;
                resultingOwnership = _out1763;
              }
              readIdents = _4599_recIdents;
            } else {
              RAST._IExpr _4601_onExpr;
              DCOMP._IOwnership _4602_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4603_recIdents;
              RAST._IExpr _out1764;
              DCOMP._IOwnership _out1765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1766;
              (this).GenExpr(_4596_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1764, out _out1765, out _out1766);
              _4601_onExpr = _out1764;
              _4602_onOwned = _out1765;
              _4603_recIdents = _out1766;
              r = _4601_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4595_field));
              if (_4594_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4604_s;
                _4604_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4601_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4595_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4604_s);
              }
              DCOMP._IOwnership _4605_fromOwnership;
              _4605_fromOwnership = ((_4594_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1767;
              DCOMP._IOwnership _out1768;
              DCOMP.COMP.FromOwnership(r, _4605_fromOwnership, expectedOwnership, out _out1767, out _out1768);
              r = _out1767;
              resultingOwnership = _out1768;
              readIdents = _4603_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Index) {
          DAST._IExpression _4606___mcc_h169 = _source178.dtor_expr;
          DAST._ICollKind _4607___mcc_h170 = _source178.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _4608___mcc_h171 = _source178.dtor_indices;
          DAST._IType _4609_fieldType = _4175___mcc_h52;
          bool _4610_isDatatype = _4174___mcc_h51;
          bool _4611_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4612_field = _4172___mcc_h49;
          DAST._IExpression _4613_on = _4171___mcc_h48;
          {
            if (_4610_isDatatype) {
              RAST._IExpr _4614_onExpr;
              DCOMP._IOwnership _4615_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4616_recIdents;
              RAST._IExpr _out1769;
              DCOMP._IOwnership _out1770;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1771;
              (this).GenExpr(_4613_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1769, out _out1770, out _out1771);
              _4614_onExpr = _out1769;
              _4615_onOwned = _out1770;
              _4616_recIdents = _out1771;
              r = ((_4614_onExpr).Sel(DCOMP.__default.escapeName(_4612_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4617_typ;
              RAST._IType _out1772;
              _out1772 = (this).GenType(_4609_fieldType, false, false);
              _4617_typ = _out1772;
              if (((_4617_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1773;
                DCOMP._IOwnership _out1774;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1773, out _out1774);
                r = _out1773;
                resultingOwnership = _out1774;
              }
              readIdents = _4616_recIdents;
            } else {
              RAST._IExpr _4618_onExpr;
              DCOMP._IOwnership _4619_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4620_recIdents;
              RAST._IExpr _out1775;
              DCOMP._IOwnership _out1776;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1777;
              (this).GenExpr(_4613_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1775, out _out1776, out _out1777);
              _4618_onExpr = _out1775;
              _4619_onOwned = _out1776;
              _4620_recIdents = _out1777;
              r = _4618_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4612_field));
              if (_4611_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4621_s;
                _4621_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4618_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4612_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4621_s);
              }
              DCOMP._IOwnership _4622_fromOwnership;
              _4622_fromOwnership = ((_4611_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1778;
              DCOMP._IOwnership _out1779;
              DCOMP.COMP.FromOwnership(r, _4622_fromOwnership, expectedOwnership, out _out1778, out _out1779);
              r = _out1778;
              resultingOwnership = _out1779;
              readIdents = _4620_recIdents;
            }
            return ;
          }
        } else if (_source178.is_IndexRange) {
          DAST._IExpression _4623___mcc_h175 = _source178.dtor_expr;
          bool _4624___mcc_h176 = _source178.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _4625___mcc_h177 = _source178.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _4626___mcc_h178 = _source178.dtor_high;
          DAST._IType _4627_fieldType = _4175___mcc_h52;
          bool _4628_isDatatype = _4174___mcc_h51;
          bool _4629_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4630_field = _4172___mcc_h49;
          DAST._IExpression _4631_on = _4171___mcc_h48;
          {
            if (_4628_isDatatype) {
              RAST._IExpr _4632_onExpr;
              DCOMP._IOwnership _4633_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4634_recIdents;
              RAST._IExpr _out1780;
              DCOMP._IOwnership _out1781;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1782;
              (this).GenExpr(_4631_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1780, out _out1781, out _out1782);
              _4632_onExpr = _out1780;
              _4633_onOwned = _out1781;
              _4634_recIdents = _out1782;
              r = ((_4632_onExpr).Sel(DCOMP.__default.escapeName(_4630_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4635_typ;
              RAST._IType _out1783;
              _out1783 = (this).GenType(_4627_fieldType, false, false);
              _4635_typ = _out1783;
              if (((_4635_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1784;
                DCOMP._IOwnership _out1785;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1784, out _out1785);
                r = _out1784;
                resultingOwnership = _out1785;
              }
              readIdents = _4634_recIdents;
            } else {
              RAST._IExpr _4636_onExpr;
              DCOMP._IOwnership _4637_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4638_recIdents;
              RAST._IExpr _out1786;
              DCOMP._IOwnership _out1787;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
              (this).GenExpr(_4631_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1786, out _out1787, out _out1788);
              _4636_onExpr = _out1786;
              _4637_onOwned = _out1787;
              _4638_recIdents = _out1788;
              r = _4636_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4630_field));
              if (_4629_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4639_s;
                _4639_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4636_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4630_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4639_s);
              }
              DCOMP._IOwnership _4640_fromOwnership;
              _4640_fromOwnership = ((_4629_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1789;
              DCOMP._IOwnership _out1790;
              DCOMP.COMP.FromOwnership(r, _4640_fromOwnership, expectedOwnership, out _out1789, out _out1790);
              r = _out1789;
              resultingOwnership = _out1790;
              readIdents = _4638_recIdents;
            }
            return ;
          }
        } else if (_source178.is_TupleSelect) {
          DAST._IExpression _4641___mcc_h183 = _source178.dtor_expr;
          BigInteger _4642___mcc_h184 = _source178.dtor_index;
          DAST._IType _4643___mcc_h185 = _source178.dtor_fieldType;
          DAST._IType _4644_fieldType = _4175___mcc_h52;
          bool _4645_isDatatype = _4174___mcc_h51;
          bool _4646_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4647_field = _4172___mcc_h49;
          DAST._IExpression _4648_on = _4171___mcc_h48;
          {
            if (_4645_isDatatype) {
              RAST._IExpr _4649_onExpr;
              DCOMP._IOwnership _4650_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4651_recIdents;
              RAST._IExpr _out1791;
              DCOMP._IOwnership _out1792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
              (this).GenExpr(_4648_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1791, out _out1792, out _out1793);
              _4649_onExpr = _out1791;
              _4650_onOwned = _out1792;
              _4651_recIdents = _out1793;
              r = ((_4649_onExpr).Sel(DCOMP.__default.escapeName(_4647_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4652_typ;
              RAST._IType _out1794;
              _out1794 = (this).GenType(_4644_fieldType, false, false);
              _4652_typ = _out1794;
              if (((_4652_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1795;
                DCOMP._IOwnership _out1796;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1795, out _out1796);
                r = _out1795;
                resultingOwnership = _out1796;
              }
              readIdents = _4651_recIdents;
            } else {
              RAST._IExpr _4653_onExpr;
              DCOMP._IOwnership _4654_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4655_recIdents;
              RAST._IExpr _out1797;
              DCOMP._IOwnership _out1798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1799;
              (this).GenExpr(_4648_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1797, out _out1798, out _out1799);
              _4653_onExpr = _out1797;
              _4654_onOwned = _out1798;
              _4655_recIdents = _out1799;
              r = _4653_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4647_field));
              if (_4646_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4656_s;
                _4656_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4653_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4647_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4656_s);
              }
              DCOMP._IOwnership _4657_fromOwnership;
              _4657_fromOwnership = ((_4646_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1800;
              DCOMP._IOwnership _out1801;
              DCOMP.COMP.FromOwnership(r, _4657_fromOwnership, expectedOwnership, out _out1800, out _out1801);
              r = _out1800;
              resultingOwnership = _out1801;
              readIdents = _4655_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Call) {
          DAST._IExpression _4658___mcc_h189 = _source178.dtor_on;
          DAST._ICallName _4659___mcc_h190 = _source178.dtor_callName;
          Dafny.ISequence<DAST._IType> _4660___mcc_h191 = _source178.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4661___mcc_h192 = _source178.dtor_args;
          DAST._IType _4662_fieldType = _4175___mcc_h52;
          bool _4663_isDatatype = _4174___mcc_h51;
          bool _4664_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4665_field = _4172___mcc_h49;
          DAST._IExpression _4666_on = _4171___mcc_h48;
          {
            if (_4663_isDatatype) {
              RAST._IExpr _4667_onExpr;
              DCOMP._IOwnership _4668_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4669_recIdents;
              RAST._IExpr _out1802;
              DCOMP._IOwnership _out1803;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1804;
              (this).GenExpr(_4666_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1802, out _out1803, out _out1804);
              _4667_onExpr = _out1802;
              _4668_onOwned = _out1803;
              _4669_recIdents = _out1804;
              r = ((_4667_onExpr).Sel(DCOMP.__default.escapeName(_4665_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4670_typ;
              RAST._IType _out1805;
              _out1805 = (this).GenType(_4662_fieldType, false, false);
              _4670_typ = _out1805;
              if (((_4670_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1806;
                DCOMP._IOwnership _out1807;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1806, out _out1807);
                r = _out1806;
                resultingOwnership = _out1807;
              }
              readIdents = _4669_recIdents;
            } else {
              RAST._IExpr _4671_onExpr;
              DCOMP._IOwnership _4672_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4673_recIdents;
              RAST._IExpr _out1808;
              DCOMP._IOwnership _out1809;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1810;
              (this).GenExpr(_4666_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1808, out _out1809, out _out1810);
              _4671_onExpr = _out1808;
              _4672_onOwned = _out1809;
              _4673_recIdents = _out1810;
              r = _4671_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4665_field));
              if (_4664_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4674_s;
                _4674_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4671_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4665_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4674_s);
              }
              DCOMP._IOwnership _4675_fromOwnership;
              _4675_fromOwnership = ((_4664_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1811;
              DCOMP._IOwnership _out1812;
              DCOMP.COMP.FromOwnership(r, _4675_fromOwnership, expectedOwnership, out _out1811, out _out1812);
              r = _out1811;
              resultingOwnership = _out1812;
              readIdents = _4673_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _4676___mcc_h197 = _source178.dtor_params;
          DAST._IType _4677___mcc_h198 = _source178.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _4678___mcc_h199 = _source178.dtor_body;
          DAST._IType _4679_fieldType = _4175___mcc_h52;
          bool _4680_isDatatype = _4174___mcc_h51;
          bool _4681_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4682_field = _4172___mcc_h49;
          DAST._IExpression _4683_on = _4171___mcc_h48;
          {
            if (_4680_isDatatype) {
              RAST._IExpr _4684_onExpr;
              DCOMP._IOwnership _4685_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4686_recIdents;
              RAST._IExpr _out1813;
              DCOMP._IOwnership _out1814;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1815;
              (this).GenExpr(_4683_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1813, out _out1814, out _out1815);
              _4684_onExpr = _out1813;
              _4685_onOwned = _out1814;
              _4686_recIdents = _out1815;
              r = ((_4684_onExpr).Sel(DCOMP.__default.escapeName(_4682_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4687_typ;
              RAST._IType _out1816;
              _out1816 = (this).GenType(_4679_fieldType, false, false);
              _4687_typ = _out1816;
              if (((_4687_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1817;
                DCOMP._IOwnership _out1818;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1817, out _out1818);
                r = _out1817;
                resultingOwnership = _out1818;
              }
              readIdents = _4686_recIdents;
            } else {
              RAST._IExpr _4688_onExpr;
              DCOMP._IOwnership _4689_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4690_recIdents;
              RAST._IExpr _out1819;
              DCOMP._IOwnership _out1820;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1821;
              (this).GenExpr(_4683_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1819, out _out1820, out _out1821);
              _4688_onExpr = _out1819;
              _4689_onOwned = _out1820;
              _4690_recIdents = _out1821;
              r = _4688_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4682_field));
              if (_4681_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4691_s;
                _4691_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4688_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4682_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4691_s);
              }
              DCOMP._IOwnership _4692_fromOwnership;
              _4692_fromOwnership = ((_4681_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1822;
              DCOMP._IOwnership _out1823;
              DCOMP.COMP.FromOwnership(r, _4692_fromOwnership, expectedOwnership, out _out1822, out _out1823);
              r = _out1822;
              resultingOwnership = _out1823;
              readIdents = _4690_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4693___mcc_h203 = _source178.dtor_values;
          DAST._IType _4694___mcc_h204 = _source178.dtor_retType;
          DAST._IExpression _4695___mcc_h205 = _source178.dtor_expr;
          DAST._IType _4696_fieldType = _4175___mcc_h52;
          bool _4697_isDatatype = _4174___mcc_h51;
          bool _4698_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4699_field = _4172___mcc_h49;
          DAST._IExpression _4700_on = _4171___mcc_h48;
          {
            if (_4697_isDatatype) {
              RAST._IExpr _4701_onExpr;
              DCOMP._IOwnership _4702_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4703_recIdents;
              RAST._IExpr _out1824;
              DCOMP._IOwnership _out1825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1826;
              (this).GenExpr(_4700_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1824, out _out1825, out _out1826);
              _4701_onExpr = _out1824;
              _4702_onOwned = _out1825;
              _4703_recIdents = _out1826;
              r = ((_4701_onExpr).Sel(DCOMP.__default.escapeName(_4699_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4704_typ;
              RAST._IType _out1827;
              _out1827 = (this).GenType(_4696_fieldType, false, false);
              _4704_typ = _out1827;
              if (((_4704_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1828;
                DCOMP._IOwnership _out1829;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1828, out _out1829);
                r = _out1828;
                resultingOwnership = _out1829;
              }
              readIdents = _4703_recIdents;
            } else {
              RAST._IExpr _4705_onExpr;
              DCOMP._IOwnership _4706_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4707_recIdents;
              RAST._IExpr _out1830;
              DCOMP._IOwnership _out1831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1832;
              (this).GenExpr(_4700_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1830, out _out1831, out _out1832);
              _4705_onExpr = _out1830;
              _4706_onOwned = _out1831;
              _4707_recIdents = _out1832;
              r = _4705_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4699_field));
              if (_4698_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4708_s;
                _4708_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4705_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4699_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4708_s);
              }
              DCOMP._IOwnership _4709_fromOwnership;
              _4709_fromOwnership = ((_4698_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1833;
              DCOMP._IOwnership _out1834;
              DCOMP.COMP.FromOwnership(r, _4709_fromOwnership, expectedOwnership, out _out1833, out _out1834);
              r = _out1833;
              resultingOwnership = _out1834;
              readIdents = _4707_recIdents;
            }
            return ;
          }
        } else if (_source178.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _4710___mcc_h209 = _source178.dtor_name;
          DAST._IType _4711___mcc_h210 = _source178.dtor_typ;
          DAST._IExpression _4712___mcc_h211 = _source178.dtor_value;
          DAST._IExpression _4713___mcc_h212 = _source178.dtor_iifeBody;
          DAST._IType _4714_fieldType = _4175___mcc_h52;
          bool _4715_isDatatype = _4174___mcc_h51;
          bool _4716_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4717_field = _4172___mcc_h49;
          DAST._IExpression _4718_on = _4171___mcc_h48;
          {
            if (_4715_isDatatype) {
              RAST._IExpr _4719_onExpr;
              DCOMP._IOwnership _4720_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4721_recIdents;
              RAST._IExpr _out1835;
              DCOMP._IOwnership _out1836;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1837;
              (this).GenExpr(_4718_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1835, out _out1836, out _out1837);
              _4719_onExpr = _out1835;
              _4720_onOwned = _out1836;
              _4721_recIdents = _out1837;
              r = ((_4719_onExpr).Sel(DCOMP.__default.escapeName(_4717_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4722_typ;
              RAST._IType _out1838;
              _out1838 = (this).GenType(_4714_fieldType, false, false);
              _4722_typ = _out1838;
              if (((_4722_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1839;
                DCOMP._IOwnership _out1840;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1839, out _out1840);
                r = _out1839;
                resultingOwnership = _out1840;
              }
              readIdents = _4721_recIdents;
            } else {
              RAST._IExpr _4723_onExpr;
              DCOMP._IOwnership _4724_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4725_recIdents;
              RAST._IExpr _out1841;
              DCOMP._IOwnership _out1842;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1843;
              (this).GenExpr(_4718_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1841, out _out1842, out _out1843);
              _4723_onExpr = _out1841;
              _4724_onOwned = _out1842;
              _4725_recIdents = _out1843;
              r = _4723_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4717_field));
              if (_4716_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4726_s;
                _4726_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4723_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4717_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4726_s);
              }
              DCOMP._IOwnership _4727_fromOwnership;
              _4727_fromOwnership = ((_4716_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1844;
              DCOMP._IOwnership _out1845;
              DCOMP.COMP.FromOwnership(r, _4727_fromOwnership, expectedOwnership, out _out1844, out _out1845);
              r = _out1844;
              resultingOwnership = _out1845;
              readIdents = _4725_recIdents;
            }
            return ;
          }
        } else if (_source178.is_Apply) {
          DAST._IExpression _4728___mcc_h217 = _source178.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _4729___mcc_h218 = _source178.dtor_args;
          DAST._IType _4730_fieldType = _4175___mcc_h52;
          bool _4731_isDatatype = _4174___mcc_h51;
          bool _4732_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4733_field = _4172___mcc_h49;
          DAST._IExpression _4734_on = _4171___mcc_h48;
          {
            if (_4731_isDatatype) {
              RAST._IExpr _4735_onExpr;
              DCOMP._IOwnership _4736_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4737_recIdents;
              RAST._IExpr _out1846;
              DCOMP._IOwnership _out1847;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1848;
              (this).GenExpr(_4734_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1846, out _out1847, out _out1848);
              _4735_onExpr = _out1846;
              _4736_onOwned = _out1847;
              _4737_recIdents = _out1848;
              r = ((_4735_onExpr).Sel(DCOMP.__default.escapeName(_4733_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4738_typ;
              RAST._IType _out1849;
              _out1849 = (this).GenType(_4730_fieldType, false, false);
              _4738_typ = _out1849;
              if (((_4738_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1850;
                DCOMP._IOwnership _out1851;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1850, out _out1851);
                r = _out1850;
                resultingOwnership = _out1851;
              }
              readIdents = _4737_recIdents;
            } else {
              RAST._IExpr _4739_onExpr;
              DCOMP._IOwnership _4740_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4741_recIdents;
              RAST._IExpr _out1852;
              DCOMP._IOwnership _out1853;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1854;
              (this).GenExpr(_4734_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1852, out _out1853, out _out1854);
              _4739_onExpr = _out1852;
              _4740_onOwned = _out1853;
              _4741_recIdents = _out1854;
              r = _4739_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4733_field));
              if (_4732_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4742_s;
                _4742_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4739_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4733_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4742_s);
              }
              DCOMP._IOwnership _4743_fromOwnership;
              _4743_fromOwnership = ((_4732_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1855;
              DCOMP._IOwnership _out1856;
              DCOMP.COMP.FromOwnership(r, _4743_fromOwnership, expectedOwnership, out _out1855, out _out1856);
              r = _out1855;
              resultingOwnership = _out1856;
              readIdents = _4741_recIdents;
            }
            return ;
          }
        } else if (_source178.is_TypeTest) {
          DAST._IExpression _4744___mcc_h221 = _source178.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4745___mcc_h222 = _source178.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _4746___mcc_h223 = _source178.dtor_variant;
          DAST._IType _4747_fieldType = _4175___mcc_h52;
          bool _4748_isDatatype = _4174___mcc_h51;
          bool _4749_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4750_field = _4172___mcc_h49;
          DAST._IExpression _4751_on = _4171___mcc_h48;
          {
            if (_4748_isDatatype) {
              RAST._IExpr _4752_onExpr;
              DCOMP._IOwnership _4753_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4754_recIdents;
              RAST._IExpr _out1857;
              DCOMP._IOwnership _out1858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1859;
              (this).GenExpr(_4751_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1857, out _out1858, out _out1859);
              _4752_onExpr = _out1857;
              _4753_onOwned = _out1858;
              _4754_recIdents = _out1859;
              r = ((_4752_onExpr).Sel(DCOMP.__default.escapeName(_4750_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4755_typ;
              RAST._IType _out1860;
              _out1860 = (this).GenType(_4747_fieldType, false, false);
              _4755_typ = _out1860;
              if (((_4755_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1861;
                DCOMP._IOwnership _out1862;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1861, out _out1862);
                r = _out1861;
                resultingOwnership = _out1862;
              }
              readIdents = _4754_recIdents;
            } else {
              RAST._IExpr _4756_onExpr;
              DCOMP._IOwnership _4757_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4758_recIdents;
              RAST._IExpr _out1863;
              DCOMP._IOwnership _out1864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1865;
              (this).GenExpr(_4751_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1863, out _out1864, out _out1865);
              _4756_onExpr = _out1863;
              _4757_onOwned = _out1864;
              _4758_recIdents = _out1865;
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
              RAST._IExpr _out1866;
              DCOMP._IOwnership _out1867;
              DCOMP.COMP.FromOwnership(r, _4760_fromOwnership, expectedOwnership, out _out1866, out _out1867);
              r = _out1866;
              resultingOwnership = _out1867;
              readIdents = _4758_recIdents;
            }
            return ;
          }
        } else if (_source178.is_InitializationValue) {
          DAST._IType _4761___mcc_h227 = _source178.dtor_typ;
          DAST._IType _4762_fieldType = _4175___mcc_h52;
          bool _4763_isDatatype = _4174___mcc_h51;
          bool _4764_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4765_field = _4172___mcc_h49;
          DAST._IExpression _4766_on = _4171___mcc_h48;
          {
            if (_4763_isDatatype) {
              RAST._IExpr _4767_onExpr;
              DCOMP._IOwnership _4768_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4769_recIdents;
              RAST._IExpr _out1868;
              DCOMP._IOwnership _out1869;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1870;
              (this).GenExpr(_4766_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1868, out _out1869, out _out1870);
              _4767_onExpr = _out1868;
              _4768_onOwned = _out1869;
              _4769_recIdents = _out1870;
              r = ((_4767_onExpr).Sel(DCOMP.__default.escapeName(_4765_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4770_typ;
              RAST._IType _out1871;
              _out1871 = (this).GenType(_4762_fieldType, false, false);
              _4770_typ = _out1871;
              if (((_4770_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1872;
                DCOMP._IOwnership _out1873;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1872, out _out1873);
                r = _out1872;
                resultingOwnership = _out1873;
              }
              readIdents = _4769_recIdents;
            } else {
              RAST._IExpr _4771_onExpr;
              DCOMP._IOwnership _4772_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4773_recIdents;
              RAST._IExpr _out1874;
              DCOMP._IOwnership _out1875;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1876;
              (this).GenExpr(_4766_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1874, out _out1875, out _out1876);
              _4771_onExpr = _out1874;
              _4772_onOwned = _out1875;
              _4773_recIdents = _out1876;
              r = _4771_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4765_field));
              if (_4764_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4774_s;
                _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4771_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4765_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4774_s);
              }
              DCOMP._IOwnership _4775_fromOwnership;
              _4775_fromOwnership = ((_4764_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1877;
              DCOMP._IOwnership _out1878;
              DCOMP.COMP.FromOwnership(r, _4775_fromOwnership, expectedOwnership, out _out1877, out _out1878);
              r = _out1877;
              resultingOwnership = _out1878;
              readIdents = _4773_recIdents;
            }
            return ;
          }
        } else if (_source178.is_BoolBoundedPool) {
          DAST._IType _4776_fieldType = _4175___mcc_h52;
          bool _4777_isDatatype = _4174___mcc_h51;
          bool _4778_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4779_field = _4172___mcc_h49;
          DAST._IExpression _4780_on = _4171___mcc_h48;
          {
            if (_4777_isDatatype) {
              RAST._IExpr _4781_onExpr;
              DCOMP._IOwnership _4782_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4783_recIdents;
              RAST._IExpr _out1879;
              DCOMP._IOwnership _out1880;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1881;
              (this).GenExpr(_4780_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1879, out _out1880, out _out1881);
              _4781_onExpr = _out1879;
              _4782_onOwned = _out1880;
              _4783_recIdents = _out1881;
              r = ((_4781_onExpr).Sel(DCOMP.__default.escapeName(_4779_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4784_typ;
              RAST._IType _out1882;
              _out1882 = (this).GenType(_4776_fieldType, false, false);
              _4784_typ = _out1882;
              if (((_4784_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1883;
                DCOMP._IOwnership _out1884;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1883, out _out1884);
                r = _out1883;
                resultingOwnership = _out1884;
              }
              readIdents = _4783_recIdents;
            } else {
              RAST._IExpr _4785_onExpr;
              DCOMP._IOwnership _4786_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4787_recIdents;
              RAST._IExpr _out1885;
              DCOMP._IOwnership _out1886;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1887;
              (this).GenExpr(_4780_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1885, out _out1886, out _out1887);
              _4785_onExpr = _out1885;
              _4786_onOwned = _out1886;
              _4787_recIdents = _out1887;
              r = _4785_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4779_field));
              if (_4778_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4788_s;
                _4788_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4785_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4779_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4788_s);
              }
              DCOMP._IOwnership _4789_fromOwnership;
              _4789_fromOwnership = ((_4778_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1888;
              DCOMP._IOwnership _out1889;
              DCOMP.COMP.FromOwnership(r, _4789_fromOwnership, expectedOwnership, out _out1888, out _out1889);
              r = _out1888;
              resultingOwnership = _out1889;
              readIdents = _4787_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SetBoundedPool) {
          DAST._IExpression _4790___mcc_h229 = _source178.dtor_of;
          DAST._IType _4791_fieldType = _4175___mcc_h52;
          bool _4792_isDatatype = _4174___mcc_h51;
          bool _4793_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4794_field = _4172___mcc_h49;
          DAST._IExpression _4795_on = _4171___mcc_h48;
          {
            if (_4792_isDatatype) {
              RAST._IExpr _4796_onExpr;
              DCOMP._IOwnership _4797_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4798_recIdents;
              RAST._IExpr _out1890;
              DCOMP._IOwnership _out1891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1892;
              (this).GenExpr(_4795_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1890, out _out1891, out _out1892);
              _4796_onExpr = _out1890;
              _4797_onOwned = _out1891;
              _4798_recIdents = _out1892;
              r = ((_4796_onExpr).Sel(DCOMP.__default.escapeName(_4794_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4799_typ;
              RAST._IType _out1893;
              _out1893 = (this).GenType(_4791_fieldType, false, false);
              _4799_typ = _out1893;
              if (((_4799_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1894;
                DCOMP._IOwnership _out1895;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1894, out _out1895);
                r = _out1894;
                resultingOwnership = _out1895;
              }
              readIdents = _4798_recIdents;
            } else {
              RAST._IExpr _4800_onExpr;
              DCOMP._IOwnership _4801_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4802_recIdents;
              RAST._IExpr _out1896;
              DCOMP._IOwnership _out1897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1898;
              (this).GenExpr(_4795_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1896, out _out1897, out _out1898);
              _4800_onExpr = _out1896;
              _4801_onOwned = _out1897;
              _4802_recIdents = _out1898;
              r = _4800_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4794_field));
              if (_4793_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4803_s;
                _4803_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4800_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4794_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4803_s);
              }
              DCOMP._IOwnership _4804_fromOwnership;
              _4804_fromOwnership = ((_4793_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1899;
              DCOMP._IOwnership _out1900;
              DCOMP.COMP.FromOwnership(r, _4804_fromOwnership, expectedOwnership, out _out1899, out _out1900);
              r = _out1899;
              resultingOwnership = _out1900;
              readIdents = _4802_recIdents;
            }
            return ;
          }
        } else if (_source178.is_SeqBoundedPool) {
          DAST._IExpression _4805___mcc_h231 = _source178.dtor_of;
          bool _4806___mcc_h232 = _source178.dtor_includeDuplicates;
          DAST._IType _4807_fieldType = _4175___mcc_h52;
          bool _4808_isDatatype = _4174___mcc_h51;
          bool _4809_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4810_field = _4172___mcc_h49;
          DAST._IExpression _4811_on = _4171___mcc_h48;
          {
            if (_4808_isDatatype) {
              RAST._IExpr _4812_onExpr;
              DCOMP._IOwnership _4813_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4814_recIdents;
              RAST._IExpr _out1901;
              DCOMP._IOwnership _out1902;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1903;
              (this).GenExpr(_4811_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1901, out _out1902, out _out1903);
              _4812_onExpr = _out1901;
              _4813_onOwned = _out1902;
              _4814_recIdents = _out1903;
              r = ((_4812_onExpr).Sel(DCOMP.__default.escapeName(_4810_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4815_typ;
              RAST._IType _out1904;
              _out1904 = (this).GenType(_4807_fieldType, false, false);
              _4815_typ = _out1904;
              if (((_4815_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1905;
                DCOMP._IOwnership _out1906;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1905, out _out1906);
                r = _out1905;
                resultingOwnership = _out1906;
              }
              readIdents = _4814_recIdents;
            } else {
              RAST._IExpr _4816_onExpr;
              DCOMP._IOwnership _4817_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4818_recIdents;
              RAST._IExpr _out1907;
              DCOMP._IOwnership _out1908;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1909;
              (this).GenExpr(_4811_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1907, out _out1908, out _out1909);
              _4816_onExpr = _out1907;
              _4817_onOwned = _out1908;
              _4818_recIdents = _out1909;
              r = _4816_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4810_field));
              if (_4809_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4819_s;
                _4819_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4816_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4810_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4819_s);
              }
              DCOMP._IOwnership _4820_fromOwnership;
              _4820_fromOwnership = ((_4809_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1910;
              DCOMP._IOwnership _out1911;
              DCOMP.COMP.FromOwnership(r, _4820_fromOwnership, expectedOwnership, out _out1910, out _out1911);
              r = _out1910;
              resultingOwnership = _out1911;
              readIdents = _4818_recIdents;
            }
            return ;
          }
        } else if (_source178.is_IntRange) {
          DAST._IExpression _4821___mcc_h235 = _source178.dtor_lo;
          DAST._IExpression _4822___mcc_h236 = _source178.dtor_hi;
          bool _4823___mcc_h237 = _source178.dtor_up;
          DAST._IType _4824_fieldType = _4175___mcc_h52;
          bool _4825_isDatatype = _4174___mcc_h51;
          bool _4826_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4827_field = _4172___mcc_h49;
          DAST._IExpression _4828_on = _4171___mcc_h48;
          {
            if (_4825_isDatatype) {
              RAST._IExpr _4829_onExpr;
              DCOMP._IOwnership _4830_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4831_recIdents;
              RAST._IExpr _out1912;
              DCOMP._IOwnership _out1913;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1914;
              (this).GenExpr(_4828_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1912, out _out1913, out _out1914);
              _4829_onExpr = _out1912;
              _4830_onOwned = _out1913;
              _4831_recIdents = _out1914;
              r = ((_4829_onExpr).Sel(DCOMP.__default.escapeName(_4827_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4832_typ;
              RAST._IType _out1915;
              _out1915 = (this).GenType(_4824_fieldType, false, false);
              _4832_typ = _out1915;
              if (((_4832_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1916;
                DCOMP._IOwnership _out1917;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1916, out _out1917);
                r = _out1916;
                resultingOwnership = _out1917;
              }
              readIdents = _4831_recIdents;
            } else {
              RAST._IExpr _4833_onExpr;
              DCOMP._IOwnership _4834_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4835_recIdents;
              RAST._IExpr _out1918;
              DCOMP._IOwnership _out1919;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1920;
              (this).GenExpr(_4828_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1918, out _out1919, out _out1920);
              _4833_onExpr = _out1918;
              _4834_onOwned = _out1919;
              _4835_recIdents = _out1920;
              r = _4833_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4827_field));
              if (_4826_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4836_s;
                _4836_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4833_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4827_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4836_s);
              }
              DCOMP._IOwnership _4837_fromOwnership;
              _4837_fromOwnership = ((_4826_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1921;
              DCOMP._IOwnership _out1922;
              DCOMP.COMP.FromOwnership(r, _4837_fromOwnership, expectedOwnership, out _out1921, out _out1922);
              r = _out1921;
              resultingOwnership = _out1922;
              readIdents = _4835_recIdents;
            }
            return ;
          }
        } else {
          DAST._IExpression _4838___mcc_h241 = _source178.dtor_start;
          bool _4839___mcc_h242 = _source178.dtor_up;
          DAST._IType _4840_fieldType = _4175___mcc_h52;
          bool _4841_isDatatype = _4174___mcc_h51;
          bool _4842_isConstant = _4173___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4843_field = _4172___mcc_h49;
          DAST._IExpression _4844_on = _4171___mcc_h48;
          {
            if (_4841_isDatatype) {
              RAST._IExpr _4845_onExpr;
              DCOMP._IOwnership _4846_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4847_recIdents;
              RAST._IExpr _out1923;
              DCOMP._IOwnership _out1924;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1925;
              (this).GenExpr(_4844_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1923, out _out1924, out _out1925);
              _4845_onExpr = _out1923;
              _4846_onOwned = _out1924;
              _4847_recIdents = _out1925;
              r = ((_4845_onExpr).Sel(DCOMP.__default.escapeName(_4843_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4848_typ;
              RAST._IType _out1926;
              _out1926 = (this).GenType(_4840_fieldType, false, false);
              _4848_typ = _out1926;
              if (((_4848_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1927;
                DCOMP._IOwnership _out1928;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1927, out _out1928);
                r = _out1927;
                resultingOwnership = _out1928;
              }
              readIdents = _4847_recIdents;
            } else {
              RAST._IExpr _4849_onExpr;
              DCOMP._IOwnership _4850_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4851_recIdents;
              RAST._IExpr _out1929;
              DCOMP._IOwnership _out1930;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1931;
              (this).GenExpr(_4844_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1929, out _out1930, out _out1931);
              _4849_onExpr = _out1929;
              _4850_onOwned = _out1930;
              _4851_recIdents = _out1931;
              r = _4849_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4843_field));
              if (_4842_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4852_s;
                _4852_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4849_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4843_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4852_s);
              }
              DCOMP._IOwnership _4853_fromOwnership;
              _4853_fromOwnership = ((_4842_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1932;
              DCOMP._IOwnership _out1933;
              DCOMP.COMP.FromOwnership(r, _4853_fromOwnership, expectedOwnership, out _out1932, out _out1933);
              r = _out1932;
              resultingOwnership = _out1933;
              readIdents = _4851_recIdents;
            }
            return ;
          }
        }
      } else if (_source175.is_SelectFn) {
        DAST._IExpression _4854___mcc_h245 = _source175.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4855___mcc_h246 = _source175.dtor_field;
        bool _4856___mcc_h247 = _source175.dtor_onDatatype;
        bool _4857___mcc_h248 = _source175.dtor_isStatic;
        BigInteger _4858___mcc_h249 = _source175.dtor_arity;
        BigInteger _4859_arity = _4858___mcc_h249;
        bool _4860_isStatic = _4857___mcc_h248;
        bool _4861_isDatatype = _4856___mcc_h247;
        Dafny.ISequence<Dafny.Rune> _4862_field = _4855___mcc_h246;
        DAST._IExpression _4863_on = _4854___mcc_h245;
        {
          RAST._IExpr _4864_onExpr;
          DCOMP._IOwnership _4865_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4866_recIdents;
          RAST._IExpr _out1934;
          DCOMP._IOwnership _out1935;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1936;
          (this).GenExpr(_4863_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1934, out _out1935, out _out1936);
          _4864_onExpr = _out1934;
          _4865_onOwned = _out1935;
          _4866_recIdents = _out1936;
          Dafny.ISequence<Dafny.Rune> _4867_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _4868_onString;
          _4868_onString = (_4864_onExpr)._ToString(DCOMP.__default.IND);
          if (_4860_isStatic) {
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4868_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_4862_field));
          } else {
            _4867_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4867_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _4868_onString), ((object.Equals(_4865_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _4869_args;
            _4869_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _4870_i;
            _4870_i = BigInteger.Zero;
            while ((_4870_i) < (_4859_arity)) {
              if ((_4870_i).Sign == 1) {
                _4869_args = Dafny.Sequence<Dafny.Rune>.Concat(_4869_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _4869_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4869_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_4870_i));
              _4870_i = (_4870_i) + (BigInteger.One);
            }
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4867_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _4869_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4867_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_4862_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4869_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(_4867_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(_4867_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _4871_typeShape;
          _4871_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _4872_i;
          _4872_i = BigInteger.Zero;
          while ((_4872_i) < (_4859_arity)) {
            if ((_4872_i).Sign == 1) {
              _4871_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4871_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _4871_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4871_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _4872_i = (_4872_i) + (BigInteger.One);
          }
          _4871_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4871_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _4867_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _4867_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _4871_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          r = RAST.Expr.create_RawExpr(_4867_s);
          RAST._IExpr _out1937;
          DCOMP._IOwnership _out1938;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1937, out _out1938);
          r = _out1937;
          resultingOwnership = _out1938;
          readIdents = _4866_recIdents;
          return ;
        }
      } else if (_source175.is_Index) {
        DAST._IExpression _4873___mcc_h250 = _source175.dtor_expr;
        DAST._ICollKind _4874___mcc_h251 = _source175.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _4875___mcc_h252 = _source175.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _4876_indices = _4875___mcc_h252;
        DAST._ICollKind _4877_collKind = _4874___mcc_h251;
        DAST._IExpression _4878_on = _4873___mcc_h250;
        {
          RAST._IExpr _4879_onExpr;
          DCOMP._IOwnership _4880_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4881_recIdents;
          RAST._IExpr _out1939;
          DCOMP._IOwnership _out1940;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1941;
          (this).GenExpr(_4878_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1939, out _out1940, out _out1941);
          _4879_onExpr = _out1939;
          _4880_onOwned = _out1940;
          _4881_recIdents = _out1941;
          readIdents = _4881_recIdents;
          r = _4879_onExpr;
          BigInteger _4882_i;
          _4882_i = BigInteger.Zero;
          while ((_4882_i) < (new BigInteger((_4876_indices).Count))) {
            if (object.Equals(_4877_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _4883_idx;
            DCOMP._IOwnership _4884_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4885_recIdentsIdx;
            RAST._IExpr _out1942;
            DCOMP._IOwnership _out1943;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1944;
            (this).GenExpr((_4876_indices).Select(_4882_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1942, out _out1943, out _out1944);
            _4883_idx = _out1942;
            _4884_idxOwned = _out1943;
            _4885_recIdentsIdx = _out1944;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_4883_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4885_recIdentsIdx);
            _4882_i = (_4882_i) + (BigInteger.One);
          }
          RAST._IExpr _out1945;
          DCOMP._IOwnership _out1946;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1945, out _out1946);
          r = _out1945;
          resultingOwnership = _out1946;
          return ;
        }
      } else if (_source175.is_IndexRange) {
        DAST._IExpression _4886___mcc_h253 = _source175.dtor_expr;
        bool _4887___mcc_h254 = _source175.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _4888___mcc_h255 = _source175.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _4889___mcc_h256 = _source175.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _4890_high = _4889___mcc_h256;
        Std.Wrappers._IOption<DAST._IExpression> _4891_low = _4888___mcc_h255;
        bool _4892_isArray = _4887___mcc_h254;
        DAST._IExpression _4893_on = _4886___mcc_h253;
        {
          RAST._IExpr _4894_onExpr;
          DCOMP._IOwnership _4895_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4896_recIdents;
          RAST._IExpr _out1947;
          DCOMP._IOwnership _out1948;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1949;
          (this).GenExpr(_4893_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1947, out _out1948, out _out1949);
          _4894_onExpr = _out1947;
          _4895_onOwned = _out1948;
          _4896_recIdents = _out1949;
          readIdents = _4896_recIdents;
          Dafny.ISequence<Dafny.Rune> _4897_methodName;
          _4897_methodName = (((_4891_low).is_Some) ? ((((_4890_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_4890_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _4898_arguments;
          _4898_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source179 = _4891_low;
          if (_source179.is_None) {
          } else {
            DAST._IExpression _4899___mcc_h289 = _source179.dtor_value;
            DAST._IExpression _4900_l = _4899___mcc_h289;
            {
              RAST._IExpr _4901_lExpr;
              DCOMP._IOwnership _4902___v142;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4903_recIdentsL;
              RAST._IExpr _out1950;
              DCOMP._IOwnership _out1951;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1952;
              (this).GenExpr(_4900_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1950, out _out1951, out _out1952);
              _4901_lExpr = _out1950;
              _4902___v142 = _out1951;
              _4903_recIdentsL = _out1952;
              _4898_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4898_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4901_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4903_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source180 = _4890_high;
          if (_source180.is_None) {
          } else {
            DAST._IExpression _4904___mcc_h290 = _source180.dtor_value;
            DAST._IExpression _4905_h = _4904___mcc_h290;
            {
              RAST._IExpr _4906_hExpr;
              DCOMP._IOwnership _4907___v143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4908_recIdentsH;
              RAST._IExpr _out1953;
              DCOMP._IOwnership _out1954;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1955;
              (this).GenExpr(_4905_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1953, out _out1954, out _out1955);
              _4906_hExpr = _out1953;
              _4907___v143 = _out1954;
              _4908_recIdentsH = _out1955;
              _4898_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4898_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4906_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4908_recIdentsH);
            }
          }
          r = _4894_onExpr;
          if (_4892_isArray) {
            if (!(_4897_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _4897_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4897_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _4897_methodName))).Apply(_4898_arguments);
          } else {
            if (!(_4897_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_4897_methodName)).Apply(_4898_arguments);
            }
          }
          RAST._IExpr _out1956;
          DCOMP._IOwnership _out1957;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1956, out _out1957);
          r = _out1956;
          resultingOwnership = _out1957;
          return ;
        }
      } else if (_source175.is_TupleSelect) {
        DAST._IExpression _4909___mcc_h257 = _source175.dtor_expr;
        BigInteger _4910___mcc_h258 = _source175.dtor_index;
        DAST._IType _4911___mcc_h259 = _source175.dtor_fieldType;
        DAST._IType _4912_fieldType = _4911___mcc_h259;
        BigInteger _4913_idx = _4910___mcc_h258;
        DAST._IExpression _4914_on = _4909___mcc_h257;
        {
          RAST._IExpr _4915_onExpr;
          DCOMP._IOwnership _4916_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4917_recIdents;
          RAST._IExpr _out1958;
          DCOMP._IOwnership _out1959;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1960;
          (this).GenExpr(_4914_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1958, out _out1959, out _out1960);
          _4915_onExpr = _out1958;
          _4916_onOwnership = _out1959;
          _4917_recIdents = _out1960;
          r = (_4915_onExpr).Sel(Std.Strings.__default.OfNat(_4913_idx));
          RAST._IExpr _out1961;
          DCOMP._IOwnership _out1962;
          DCOMP.COMP.FromOwnership(r, _4916_onOwnership, expectedOwnership, out _out1961, out _out1962);
          r = _out1961;
          resultingOwnership = _out1962;
          readIdents = _4917_recIdents;
          return ;
        }
      } else if (_source175.is_Call) {
        DAST._IExpression _4918___mcc_h260 = _source175.dtor_on;
        DAST._ICallName _4919___mcc_h261 = _source175.dtor_callName;
        Dafny.ISequence<DAST._IType> _4920___mcc_h262 = _source175.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _4921___mcc_h263 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4922_args = _4921___mcc_h263;
        Dafny.ISequence<DAST._IType> _4923_typeArgs = _4920___mcc_h262;
        DAST._ICallName _4924_name = _4919___mcc_h261;
        DAST._IExpression _4925_on = _4918___mcc_h260;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _4926_onExpr;
          DCOMP._IOwnership _4927___v144;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4928_recIdents;
          RAST._IExpr _out1963;
          DCOMP._IOwnership _out1964;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1965;
          (this).GenExpr(_4925_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1963, out _out1964, out _out1965);
          _4926_onExpr = _out1963;
          _4927___v144 = _out1964;
          _4928_recIdents = _out1965;
          Dafny.ISequence<RAST._IType> _4929_typeExprs;
          _4929_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_4923_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _hi35 = new BigInteger((_4923_typeArgs).Count);
            for (BigInteger _4930_typeI = BigInteger.Zero; _4930_typeI < _hi35; _4930_typeI++) {
              RAST._IType _4931_typeExpr;
              RAST._IType _out1966;
              _out1966 = (this).GenType((_4923_typeArgs).Select(_4930_typeI), false, false);
              _4931_typeExpr = _out1966;
              _4929_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4929_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_4931_typeExpr));
            }
          }
          Dafny.ISequence<RAST._IExpr> _4932_argExprs;
          _4932_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi36 = new BigInteger((_4922_args).Count);
          for (BigInteger _4933_i = BigInteger.Zero; _4933_i < _hi36; _4933_i++) {
            DCOMP._IOwnership _4934_argOwnership;
            _4934_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_4924_name).is_CallName) && ((_4933_i) < (new BigInteger((((_4924_name).dtor_signature)).Count)))) {
              RAST._IType _4935_tpe;
              RAST._IType _out1967;
              _out1967 = (this).GenType(((((_4924_name).dtor_signature)).Select(_4933_i)).dtor_typ, false, false);
              _4935_tpe = _out1967;
              if ((_4935_tpe).CanReadWithoutClone()) {
                _4934_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _4936_argExpr;
            DCOMP._IOwnership _4937___v145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4938_argIdents;
            RAST._IExpr _out1968;
            DCOMP._IOwnership _out1969;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1970;
            (this).GenExpr((_4922_args).Select(_4933_i), selfIdent, env, _4934_argOwnership, out _out1968, out _out1969, out _out1970);
            _4936_argExpr = _out1968;
            _4937___v145 = _out1969;
            _4938_argIdents = _out1970;
            _4932_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_4932_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4936_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4938_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4928_recIdents);
          Dafny.ISequence<Dafny.Rune> _4939_renderedName;
          _4939_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source181) => {
            if (_source181.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _4940___mcc_h291 = _source181.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _4941___mcc_h292 = _source181.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _4942___mcc_h293 = _source181.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _4943_ident = _4940___mcc_h291;
              return DCOMP.__default.escapeName(_4943_ident);
            } else if (_source181.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source181.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source181.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_4924_name);
          DAST._IExpression _source182 = _4925_on;
          if (_source182.is_Literal) {
            DAST._ILiteral _4944___mcc_h294 = _source182.dtor_Literal_i_a0;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _4945___mcc_h296 = _source182.dtor_Ident_i_a0;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4946___mcc_h298 = _source182.dtor_Companion_i_a0;
            {
              _4926_onExpr = (_4926_onExpr).MSel(_4939_renderedName);
            }
          } else if (_source182.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _4947___mcc_h300 = _source182.dtor_Tuple_i_a0;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4948___mcc_h302 = _source182.dtor_path;
            Dafny.ISequence<DAST._IType> _4949___mcc_h303 = _source182.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4950___mcc_h304 = _source182.dtor_args;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _4951___mcc_h308 = _source182.dtor_dims;
            DAST._IType _4952___mcc_h309 = _source182.dtor_typ;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_DatatypeValue) {
            DAST._IDatatypeType _4953___mcc_h312 = _source182.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _4954___mcc_h313 = _source182.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _4955___mcc_h314 = _source182.dtor_variant;
            bool _4956___mcc_h315 = _source182.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4957___mcc_h316 = _source182.dtor_contents;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Convert) {
            DAST._IExpression _4958___mcc_h322 = _source182.dtor_value;
            DAST._IType _4959___mcc_h323 = _source182.dtor_from;
            DAST._IType _4960___mcc_h324 = _source182.dtor_typ;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SeqConstruct) {
            DAST._IExpression _4961___mcc_h328 = _source182.dtor_length;
            DAST._IExpression _4962___mcc_h329 = _source182.dtor_elem;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _4963___mcc_h332 = _source182.dtor_elements;
            DAST._IType _4964___mcc_h333 = _source182.dtor_typ;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _4965___mcc_h336 = _source182.dtor_elements;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _4966___mcc_h338 = _source182.dtor_elements;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4967___mcc_h340 = _source182.dtor_mapElems;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MapBuilder) {
            DAST._IType _4968___mcc_h342 = _source182.dtor_keyType;
            DAST._IType _4969___mcc_h343 = _source182.dtor_valueType;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SeqUpdate) {
            DAST._IExpression _4970___mcc_h346 = _source182.dtor_expr;
            DAST._IExpression _4971___mcc_h347 = _source182.dtor_indexExpr;
            DAST._IExpression _4972___mcc_h348 = _source182.dtor_value;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MapUpdate) {
            DAST._IExpression _4973___mcc_h352 = _source182.dtor_expr;
            DAST._IExpression _4974___mcc_h353 = _source182.dtor_indexExpr;
            DAST._IExpression _4975___mcc_h354 = _source182.dtor_value;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SetBuilder) {
            DAST._IType _4976___mcc_h358 = _source182.dtor_elemType;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_ToMultiset) {
            DAST._IExpression _4977___mcc_h360 = _source182.dtor_ToMultiset_i_a0;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_This) {
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Ite) {
            DAST._IExpression _4978___mcc_h362 = _source182.dtor_cond;
            DAST._IExpression _4979___mcc_h363 = _source182.dtor_thn;
            DAST._IExpression _4980___mcc_h364 = _source182.dtor_els;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_UnOp) {
            DAST._IUnaryOp _4981___mcc_h368 = _source182.dtor_unOp;
            DAST._IExpression _4982___mcc_h369 = _source182.dtor_expr;
            DAST.Format._IUnaryOpFormat _4983___mcc_h370 = _source182.dtor_format1;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_BinOp) {
            DAST._IBinOp _4984___mcc_h374 = _source182.dtor_op;
            DAST._IExpression _4985___mcc_h375 = _source182.dtor_left;
            DAST._IExpression _4986___mcc_h376 = _source182.dtor_right;
            DAST.Format._IBinaryOpFormat _4987___mcc_h377 = _source182.dtor_format2;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_ArrayLen) {
            DAST._IExpression _4988___mcc_h382 = _source182.dtor_expr;
            BigInteger _4989___mcc_h383 = _source182.dtor_dim;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MapKeys) {
            DAST._IExpression _4990___mcc_h386 = _source182.dtor_expr;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_MapValues) {
            DAST._IExpression _4991___mcc_h388 = _source182.dtor_expr;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Select) {
            DAST._IExpression _4992___mcc_h390 = _source182.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4993___mcc_h391 = _source182.dtor_field;
            bool _4994___mcc_h392 = _source182.dtor_isConstant;
            bool _4995___mcc_h393 = _source182.dtor_onDatatype;
            DAST._IType _4996___mcc_h394 = _source182.dtor_fieldType;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SelectFn) {
            DAST._IExpression _4997___mcc_h400 = _source182.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4998___mcc_h401 = _source182.dtor_field;
            bool _4999___mcc_h402 = _source182.dtor_onDatatype;
            bool _5000___mcc_h403 = _source182.dtor_isStatic;
            BigInteger _5001___mcc_h404 = _source182.dtor_arity;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Index) {
            DAST._IExpression _5002___mcc_h410 = _source182.dtor_expr;
            DAST._ICollKind _5003___mcc_h411 = _source182.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _5004___mcc_h412 = _source182.dtor_indices;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_IndexRange) {
            DAST._IExpression _5005___mcc_h416 = _source182.dtor_expr;
            bool _5006___mcc_h417 = _source182.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _5007___mcc_h418 = _source182.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _5008___mcc_h419 = _source182.dtor_high;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_TupleSelect) {
            DAST._IExpression _5009___mcc_h424 = _source182.dtor_expr;
            BigInteger _5010___mcc_h425 = _source182.dtor_index;
            DAST._IType _5011___mcc_h426 = _source182.dtor_fieldType;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Call) {
            DAST._IExpression _5012___mcc_h430 = _source182.dtor_on;
            DAST._ICallName _5013___mcc_h431 = _source182.dtor_callName;
            Dafny.ISequence<DAST._IType> _5014___mcc_h432 = _source182.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _5015___mcc_h433 = _source182.dtor_args;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _5016___mcc_h438 = _source182.dtor_params;
            DAST._IType _5017___mcc_h439 = _source182.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _5018___mcc_h440 = _source182.dtor_body;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5019___mcc_h444 = _source182.dtor_values;
            DAST._IType _5020___mcc_h445 = _source182.dtor_retType;
            DAST._IExpression _5021___mcc_h446 = _source182.dtor_expr;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _5022___mcc_h450 = _source182.dtor_name;
            DAST._IType _5023___mcc_h451 = _source182.dtor_typ;
            DAST._IExpression _5024___mcc_h452 = _source182.dtor_value;
            DAST._IExpression _5025___mcc_h453 = _source182.dtor_iifeBody;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_Apply) {
            DAST._IExpression _5026___mcc_h458 = _source182.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _5027___mcc_h459 = _source182.dtor_args;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_TypeTest) {
            DAST._IExpression _5028___mcc_h462 = _source182.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5029___mcc_h463 = _source182.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _5030___mcc_h464 = _source182.dtor_variant;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_InitializationValue) {
            DAST._IType _5031___mcc_h468 = _source182.dtor_typ;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_BoolBoundedPool) {
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SetBoundedPool) {
            DAST._IExpression _5032___mcc_h470 = _source182.dtor_of;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_SeqBoundedPool) {
            DAST._IExpression _5033___mcc_h472 = _source182.dtor_of;
            bool _5034___mcc_h473 = _source182.dtor_includeDuplicates;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else if (_source182.is_IntRange) {
            DAST._IExpression _5035___mcc_h476 = _source182.dtor_lo;
            DAST._IExpression _5036___mcc_h477 = _source182.dtor_hi;
            bool _5037___mcc_h478 = _source182.dtor_up;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          } else {
            DAST._IExpression _5038___mcc_h482 = _source182.dtor_start;
            bool _5039___mcc_h483 = _source182.dtor_up;
            {
              _4926_onExpr = (_4926_onExpr).Sel(_4939_renderedName);
            }
          }
          r = _4926_onExpr;
          if ((new BigInteger((_4929_typeExprs).Count)).Sign == 1) {
            r = (r).ApplyType(_4929_typeExprs);
          }
          r = (r).Apply(_4932_argExprs);
          RAST._IExpr _out1971;
          DCOMP._IOwnership _out1972;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1971, out _out1972);
          r = _out1971;
          resultingOwnership = _out1972;
          return ;
        }
      } else if (_source175.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _5040___mcc_h264 = _source175.dtor_params;
        DAST._IType _5041___mcc_h265 = _source175.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _5042___mcc_h266 = _source175.dtor_body;
        Dafny.ISequence<DAST._IStatement> _5043_body = _5042___mcc_h266;
        DAST._IType _5044_retType = _5041___mcc_h265;
        Dafny.ISequence<DAST._IFormal> _5045_paramsDafny = _5040___mcc_h264;
        {
          Dafny.ISequence<RAST._IFormal> _5046_params;
          Dafny.ISequence<RAST._IFormal> _out1973;
          _out1973 = (this).GenParams(_5045_paramsDafny);
          _5046_params = _out1973;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5047_paramNames;
          _5047_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5048_paramTypesMap;
          _5048_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          BigInteger _hi37 = new BigInteger((_5046_params).Count);
          for (BigInteger _5049_i = BigInteger.Zero; _5049_i < _hi37; _5049_i++) {
            Dafny.ISequence<Dafny.Rune> _5050_name;
            _5050_name = ((_5046_params).Select(_5049_i)).dtor_name;
            _5047_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5047_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5050_name));
            _5048_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5048_paramTypesMap, _5050_name, ((_5046_params).Select(_5049_i)).dtor_tpe);
          }
          DCOMP._IEnvironment _5051_env;
          _5051_env = DCOMP.Environment.create(_5047_paramNames, _5048_paramTypesMap);
          RAST._IExpr _5052_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5053_recIdents;
          DCOMP._IEnvironment _5054___v150;
          RAST._IExpr _out1974;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1975;
          DCOMP._IEnvironment _out1976;
          (this).GenStmts(_5043_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _5051_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1974, out _out1975, out _out1976);
          _5052_recursiveGen = _out1974;
          _5053_recIdents = _out1975;
          _5054___v150 = _out1976;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          _5053_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5053_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_5055_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
            var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
            foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_5055_paramNames).CloneAsArray()) {
              Dafny.ISequence<Dafny.Rune> _5056_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
              if ((_5055_paramNames).Contains(_5056_name)) {
                _coll6.Add(_5056_name);
              }
            }
            return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
          }))())(_5047_paramNames));
          RAST._IExpr _5057_allReadCloned;
          _5057_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          while (!(_5053_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _5058_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_5053_recIdents).Elements) {
              _5058_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_5053_recIdents).Contains(_5058_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3733)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_5058_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _5057_allReadCloned = (_5057_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              }
            } else if (!((_5047_paramNames).Contains(_5058_next))) {
              _5057_allReadCloned = (_5057_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _5058_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_5058_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5058_next));
            }
            _5053_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5053_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5058_next));
          }
          RAST._IType _5059_retTypeGen;
          RAST._IType _out1977;
          _out1977 = (this).GenType(_5044_retType, false, true);
          _5059_retTypeGen = _out1977;
          r = RAST.Expr.create_Block((_5057_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_5046_params, Std.Wrappers.Option<RAST._IType>.create_Some(_5059_retTypeGen), RAST.Expr.create_Block(_5052_recursiveGen)))));
          RAST._IExpr _out1978;
          DCOMP._IOwnership _out1979;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1978, out _out1979);
          r = _out1978;
          resultingOwnership = _out1979;
          return ;
        }
      } else if (_source175.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5060___mcc_h267 = _source175.dtor_values;
        DAST._IType _5061___mcc_h268 = _source175.dtor_retType;
        DAST._IExpression _5062___mcc_h269 = _source175.dtor_expr;
        DAST._IExpression _5063_expr = _5062___mcc_h269;
        DAST._IType _5064_retType = _5061___mcc_h268;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _5065_values = _5060___mcc_h267;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5066_paramNames;
          _5066_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IFormal> _5067_paramFormals;
          Dafny.ISequence<RAST._IFormal> _out1980;
          _out1980 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_5068_value) => {
            return (_5068_value).dtor__0;
          })), _5065_values));
          _5067_paramFormals = _out1980;
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _5069_paramTypes;
          _5069_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5070_paramNamesSet;
          _5070_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi38 = new BigInteger((_5065_values).Count);
          for (BigInteger _5071_i = BigInteger.Zero; _5071_i < _hi38; _5071_i++) {
            Dafny.ISequence<Dafny.Rune> _5072_name;
            _5072_name = (((_5065_values).Select(_5071_i)).dtor__0).dtor_name;
            Dafny.ISequence<Dafny.Rune> _5073_rName;
            _5073_rName = DCOMP.__default.escapeName(_5072_name);
            _5066_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_5066_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_5073_rName));
            _5069_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_5069_paramTypes, _5073_rName, ((_5067_paramFormals).Select(_5071_i)).dtor_tpe);
            _5070_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5070_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5073_rName));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          BigInteger _hi39 = new BigInteger((_5065_values).Count);
          for (BigInteger _5074_i = BigInteger.Zero; _5074_i < _hi39; _5074_i++) {
            RAST._IType _5075_typeGen;
            RAST._IType _out1981;
            _out1981 = (this).GenType((((_5065_values).Select(_5074_i)).dtor__0).dtor_typ, false, true);
            _5075_typeGen = _out1981;
            RAST._IExpr _5076_valueGen;
            DCOMP._IOwnership _5077___v151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5078_recIdents;
            RAST._IExpr _out1982;
            DCOMP._IOwnership _out1983;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1984;
            (this).GenExpr(((_5065_values).Select(_5074_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1982, out _out1983, out _out1984);
            _5076_valueGen = _out1982;
            _5077___v151 = _out1983;
            _5078_recIdents = _out1984;
            r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_5065_values).Select(_5074_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_5075_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5076_valueGen)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5078_recIdents);
          }
          DCOMP._IEnvironment _5079_newEnv;
          _5079_newEnv = DCOMP.Environment.create(_5066_paramNames, _5069_paramTypes);
          RAST._IExpr _5080_recGen;
          DCOMP._IOwnership _5081_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5082_recIdents;
          RAST._IExpr _out1985;
          DCOMP._IOwnership _out1986;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1987;
          (this).GenExpr(_5063_expr, selfIdent, _5079_newEnv, expectedOwnership, out _out1985, out _out1986, out _out1987);
          _5080_recGen = _out1985;
          _5081_recOwned = _out1986;
          _5082_recIdents = _out1987;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5082_recIdents, _5070_paramNamesSet);
          r = RAST.Expr.create_Block((r).Then(_5080_recGen));
          RAST._IExpr _out1988;
          DCOMP._IOwnership _out1989;
          DCOMP.COMP.FromOwnership(r, _5081_recOwned, expectedOwnership, out _out1988, out _out1989);
          r = _out1988;
          resultingOwnership = _out1989;
          return ;
        }
      } else if (_source175.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _5083___mcc_h270 = _source175.dtor_name;
        DAST._IType _5084___mcc_h271 = _source175.dtor_typ;
        DAST._IExpression _5085___mcc_h272 = _source175.dtor_value;
        DAST._IExpression _5086___mcc_h273 = _source175.dtor_iifeBody;
        DAST._IExpression _5087_iifeBody = _5086___mcc_h273;
        DAST._IExpression _5088_value = _5085___mcc_h272;
        DAST._IType _5089_tpe = _5084___mcc_h271;
        Dafny.ISequence<Dafny.Rune> _5090_name = _5083___mcc_h270;
        {
          RAST._IExpr _5091_valueGen;
          DCOMP._IOwnership _5092___v152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5093_recIdents;
          RAST._IExpr _out1990;
          DCOMP._IOwnership _out1991;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1992;
          (this).GenExpr(_5088_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1990, out _out1991, out _out1992);
          _5091_valueGen = _out1990;
          _5092___v152 = _out1991;
          _5093_recIdents = _out1992;
          readIdents = _5093_recIdents;
          RAST._IType _5094_valueTypeGen;
          RAST._IType _out1993;
          _out1993 = (this).GenType(_5089_tpe, false, true);
          _5094_valueTypeGen = _out1993;
          RAST._IExpr _5095_bodyGen;
          DCOMP._IOwnership _5096___v153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5097_bodyIdents;
          RAST._IExpr _out1994;
          DCOMP._IOwnership _out1995;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1996;
          (this).GenExpr(_5087_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1994, out _out1995, out _out1996);
          _5095_bodyGen = _out1994;
          _5096___v153 = _out1995;
          _5097_bodyIdents = _out1996;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5097_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_5090_name)))));
          r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_5090_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_5094_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5091_valueGen))).Then(_5095_bodyGen));
          RAST._IExpr _out1997;
          DCOMP._IOwnership _out1998;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1997, out _out1998);
          r = _out1997;
          resultingOwnership = _out1998;
          return ;
        }
      } else if (_source175.is_Apply) {
        DAST._IExpression _5098___mcc_h274 = _source175.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _5099___mcc_h275 = _source175.dtor_args;
        Dafny.ISequence<DAST._IExpression> _5100_args = _5099___mcc_h275;
        DAST._IExpression _5101_func = _5098___mcc_h274;
        {
          RAST._IExpr _5102_funcExpr;
          DCOMP._IOwnership _5103___v154;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5104_recIdents;
          RAST._IExpr _out1999;
          DCOMP._IOwnership _out2000;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2001;
          (this).GenExpr(_5101_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1999, out _out2000, out _out2001);
          _5102_funcExpr = _out1999;
          _5103___v154 = _out2000;
          _5104_recIdents = _out2001;
          readIdents = _5104_recIdents;
          Dafny.ISequence<RAST._IExpr> _5105_rArgs;
          _5105_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi40 = new BigInteger((_5100_args).Count);
          for (BigInteger _5106_i = BigInteger.Zero; _5106_i < _hi40; _5106_i++) {
            RAST._IExpr _5107_argExpr;
            DCOMP._IOwnership _5108_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5109_argIdents;
            RAST._IExpr _out2002;
            DCOMP._IOwnership _out2003;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2004;
            (this).GenExpr((_5100_args).Select(_5106_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2002, out _out2003, out _out2004);
            _5107_argExpr = _out2002;
            _5108_argOwned = _out2003;
            _5109_argIdents = _out2004;
            _5105_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_5105_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_5107_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5109_argIdents);
          }
          r = (_5102_funcExpr).Apply(_5105_rArgs);
          RAST._IExpr _out2005;
          DCOMP._IOwnership _out2006;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2005, out _out2006);
          r = _out2005;
          resultingOwnership = _out2006;
          return ;
        }
      } else if (_source175.is_TypeTest) {
        DAST._IExpression _5110___mcc_h276 = _source175.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5111___mcc_h277 = _source175.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _5112___mcc_h278 = _source175.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _5113_variant = _5112___mcc_h278;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5114_dType = _5111___mcc_h277;
        DAST._IExpression _5115_on = _5110___mcc_h276;
        {
          RAST._IExpr _5116_exprGen;
          DCOMP._IOwnership _5117___v155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5118_recIdents;
          RAST._IExpr _out2007;
          DCOMP._IOwnership _out2008;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2009;
          (this).GenExpr(_5115_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2007, out _out2008, out _out2009);
          _5116_exprGen = _out2007;
          _5117___v155 = _out2008;
          _5118_recIdents = _out2009;
          RAST._IType _5119_dTypePath;
          RAST._IType _out2010;
          _out2010 = DCOMP.COMP.GenPath(_5114_dType);
          _5119_dTypePath = _out2010;
          r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_5116_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_5119_dTypePath).MSel(DCOMP.__default.escapeName(_5113_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
          RAST._IExpr _out2011;
          DCOMP._IOwnership _out2012;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2011, out _out2012);
          r = _out2011;
          resultingOwnership = _out2012;
          readIdents = _5118_recIdents;
          return ;
        }
      } else if (_source175.is_InitializationValue) {
        DAST._IType _5120___mcc_h279 = _source175.dtor_typ;
        DAST._IType _5121_typ = _5120___mcc_h279;
        {
          RAST._IType _5122_typExpr;
          RAST._IType _out2013;
          _out2013 = (this).GenType(_5121_typ, false, false);
          _5122_typExpr = _out2013;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_5122_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out2014;
          DCOMP._IOwnership _out2015;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2014, out _out2015);
          r = _out2014;
          resultingOwnership = _out2015;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_BoolBoundedPool) {
        {
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
          RAST._IExpr _out2016;
          DCOMP._IOwnership _out2017;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2016, out _out2017);
          r = _out2016;
          resultingOwnership = _out2017;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source175.is_SetBoundedPool) {
        DAST._IExpression _5123___mcc_h280 = _source175.dtor_of;
        DAST._IExpression _5124_of = _5123___mcc_h280;
        {
          RAST._IExpr _5125_exprGen;
          DCOMP._IOwnership _5126___v156;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5127_recIdents;
          RAST._IExpr _out2018;
          DCOMP._IOwnership _out2019;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2020;
          (this).GenExpr(_5124_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2018, out _out2019, out _out2020);
          _5125_exprGen = _out2018;
          _5126___v156 = _out2019;
          _5127_recIdents = _out2020;
          r = ((((_5125_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out2021;
          DCOMP._IOwnership _out2022;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2021, out _out2022);
          r = _out2021;
          resultingOwnership = _out2022;
          readIdents = _5127_recIdents;
          return ;
        }
      } else if (_source175.is_SeqBoundedPool) {
        DAST._IExpression _5128___mcc_h281 = _source175.dtor_of;
        bool _5129___mcc_h282 = _source175.dtor_includeDuplicates;
        bool _5130_includeDuplicates = _5129___mcc_h282;
        DAST._IExpression _5131_of = _5128___mcc_h281;
        {
          RAST._IExpr _5132_exprGen;
          DCOMP._IOwnership _5133___v157;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5134_recIdents;
          RAST._IExpr _out2023;
          DCOMP._IOwnership _out2024;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2025;
          (this).GenExpr(_5131_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out2023, out _out2024, out _out2025);
          _5132_exprGen = _out2023;
          _5133___v157 = _out2024;
          _5134_recIdents = _out2025;
          r = ((_5132_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          if (!(_5130_includeDuplicates)) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
          }
          RAST._IExpr _out2026;
          DCOMP._IOwnership _out2027;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2026, out _out2027);
          r = _out2026;
          resultingOwnership = _out2027;
          readIdents = _5134_recIdents;
          return ;
        }
      } else if (_source175.is_IntRange) {
        DAST._IExpression _5135___mcc_h283 = _source175.dtor_lo;
        DAST._IExpression _5136___mcc_h284 = _source175.dtor_hi;
        bool _5137___mcc_h285 = _source175.dtor_up;
        bool _5138_up = _5137___mcc_h285;
        DAST._IExpression _5139_hi = _5136___mcc_h284;
        DAST._IExpression _5140_lo = _5135___mcc_h283;
        {
          RAST._IExpr _5141_lo;
          DCOMP._IOwnership _5142___v158;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5143_recIdentsLo;
          RAST._IExpr _out2028;
          DCOMP._IOwnership _out2029;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2030;
          (this).GenExpr(_5140_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2028, out _out2029, out _out2030);
          _5141_lo = _out2028;
          _5142___v158 = _out2029;
          _5143_recIdentsLo = _out2030;
          RAST._IExpr _5144_hi;
          DCOMP._IOwnership _5145___v159;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5146_recIdentsHi;
          RAST._IExpr _out2031;
          DCOMP._IOwnership _out2032;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2033;
          (this).GenExpr(_5139_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2031, out _out2032, out _out2033);
          _5144_hi = _out2031;
          _5145___v159 = _out2032;
          _5146_recIdentsHi = _out2033;
          if (_5138_up) {
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_5141_lo, _5144_hi));
          } else {
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_5144_hi, _5141_lo));
          }
          RAST._IExpr _out2034;
          DCOMP._IOwnership _out2035;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2034, out _out2035);
          r = _out2034;
          resultingOwnership = _out2035;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5143_recIdentsLo, _5146_recIdentsHi);
          return ;
        }
      } else {
        DAST._IExpression _5147___mcc_h286 = _source175.dtor_start;
        bool _5148___mcc_h287 = _source175.dtor_up;
        bool _5149_up = _5148___mcc_h287;
        DAST._IExpression _5150_start = _5147___mcc_h286;
        {
          RAST._IExpr _5151_start;
          DCOMP._IOwnership _5152___v160;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5153_recIdentStart;
          RAST._IExpr _out2036;
          DCOMP._IOwnership _out2037;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2038;
          (this).GenExpr(_5150_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2036, out _out2037, out _out2038);
          _5151_start = _out2036;
          _5152___v160 = _out2037;
          _5153_recIdentStart = _out2038;
          if (_5149_up) {
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_5151_start);
          } else {
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_5151_start);
          }
          RAST._IExpr _out2039;
          DCOMP._IOwnership _out2040;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2039, out _out2040);
          r = _out2039;
          resultingOwnership = _out2040;
          readIdents = _5153_recIdentStart;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _5154_i;
      _5154_i = BigInteger.Zero;
      while ((_5154_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _5155_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _5156_m;
        RAST._IMod _out2041;
        _out2041 = (this).GenModule((p).Select(_5154_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _5156_m = _out2041;
        _5155_generated = (_5156_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_5154_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _5155_generated);
        _5154_i = (_5154_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _5157_i;
      _5157_i = BigInteger.Zero;
      while ((_5157_i) < (new BigInteger((fullName).Count))) {
        if ((_5157_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_5157_i)));
        _5157_i = (_5157_i) + (BigInteger.One);
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