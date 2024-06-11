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
      Dafny.ISequence<Dafny.Rune> _1029___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1029___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1029___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1029___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _1029___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1029___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1030___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1030___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1030___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1030___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _1030___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1030___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1031_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1031_r);
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
      BigInteger _1032_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1032_indexInEnv), ((this).dtor_names).Drop((_1032_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this._UnicodeChars = false;
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars)
    {
      (this)._UnicodeChars = unicodeChars;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1033_modName;
      _1033_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1033_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1034_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1034_body = _out15;
        s = RAST.Mod.create_Mod(_1033_modName, _1034_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1035_i = BigInteger.Zero; _1035_i < _hi5; _1035_i++) {
        Dafny.ISequence<RAST._IModDecl> _1036_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source44 = (body).Select(_1035_i);
        bool unmatched44 = true;
        if (unmatched44) {
          if (_source44.is_Module) {
            DAST._IModule _1037_m = _source44.dtor_Module_a0;
            unmatched44 = false;
            RAST._IMod _1038_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1037_m, containingPath);
            _1038_mm = _out16;
            _1036_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1038_mm));
          }
        }
        if (unmatched44) {
          if (_source44.is_Class) {
            DAST._IClass _1039_c = _source44.dtor_Class_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1039_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1039_c).dtor_name)));
            _1036_generated = _out17;
          }
        }
        if (unmatched44) {
          if (_source44.is_Trait) {
            DAST._ITrait _1040_t = _source44.dtor_Trait_a0;
            unmatched44 = false;
            Dafny.ISequence<Dafny.Rune> _1041_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_1040_t, containingPath);
            _1041_tt = _out18;
            _1036_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1041_tt));
          }
        }
        if (unmatched44) {
          if (_source44.is_Newtype) {
            DAST._INewtype _1042_n = _source44.dtor_Newtype_a0;
            unmatched44 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1042_n);
            _1036_generated = _out19;
          }
        }
        if (unmatched44) {
          DAST._IDatatype _1043_d = _source44.dtor_Datatype_a0;
          unmatched44 = false;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1043_d);
          _1036_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1036_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1044_genTpConstraint;
      _1044_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1044_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1044_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1044_genTpConstraint);
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
        for (BigInteger _1045_tpI = BigInteger.Zero; _1045_tpI < _hi6; _1045_tpI++) {
          DAST._ITypeArgDecl _1046_tp;
          _1046_tp = (@params).Select(_1045_tpI);
          DAST._IType _1047_typeArg;
          RAST._ITypeParamDecl _1048_typeParam;
          DAST._IType _out21;
          RAST._ITypeParamDecl _out22;
          (this).GenTypeParam(_1046_tp, out _out21, out _out22);
          _1047_typeArg = _out21;
          _1048_typeParam = _out22;
          RAST._IType _1049_rType;
          RAST._IType _out23;
          _out23 = (this).GenType(_1047_typeArg, false, false);
          _1049_rType = _out23;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1047_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1049_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1048_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1050_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1051_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1052_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1053_whereConstraints;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<RAST._IType> _out25;
      Dafny.ISequence<RAST._ITypeParamDecl> _out26;
      Dafny.ISequence<Dafny.Rune> _out27;
      (this).GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26, out _out27);
      _1050_typeParamsSet = _out24;
      _1051_rTypeParams = _out25;
      _1052_rTypeParamsDecls = _out26;
      _1053_whereConstraints = _out27;
      Dafny.ISequence<Dafny.Rune> _1054_constrainedTypeParams;
      _1054_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1052_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1055_fields;
      _1055_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1056_fieldInits;
      _1056_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1057_fieldI = BigInteger.Zero; _1057_fieldI < _hi7; _1057_fieldI++) {
        DAST._IField _1058_field;
        _1058_field = ((c).dtor_fields).Select(_1057_fieldI);
        RAST._IType _1059_fieldType;
        RAST._IType _out28;
        _out28 = (this).GenType(((_1058_field).dtor_formal).dtor_typ, false, false);
        _1059_fieldType = _out28;
        Dafny.ISequence<Dafny.Rune> _1060_fieldRustName;
        _1060_fieldRustName = DCOMP.__default.escapeName(((_1058_field).dtor_formal).dtor_name);
        _1055_fields = Dafny.Sequence<RAST._IField>.Concat(_1055_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1060_fieldRustName, _1059_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1058_field).dtor_defaultValue;
        bool unmatched45 = true;
        if (unmatched45) {
          if (_source45.is_Some) {
            DAST._IExpression _1061_e = _source45.dtor_value;
            unmatched45 = false;
            {
              RAST._IExpr _1062_expr;
              DCOMP._IOwnership _1063___v39;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1064___v40;
              RAST._IExpr _out29;
              DCOMP._IOwnership _out30;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
              (this).GenExpr(_1061_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out29, out _out30, out _out31);
              _1062_expr = _out29;
              _1063___v39 = _out30;
              _1064___v40 = _out31;
              _1056_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1056_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1058_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1062_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched45) {
          unmatched45 = false;
          {
            RAST._IExpr _1065_default;
            _1065_default = RAST.__default.std__Default__default;
            _1056_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1056_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1060_fieldRustName, _1065_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1066_typeParamI = BigInteger.Zero; _1066_typeParamI < _hi8; _1066_typeParamI++) {
        DAST._IType _1067_typeArg;
        RAST._ITypeParamDecl _1068_typeParam;
        DAST._IType _out32;
        RAST._ITypeParamDecl _out33;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1066_typeParamI), out _out32, out _out33);
        _1067_typeArg = _out32;
        _1068_typeParam = _out33;
        RAST._IType _1069_rTypeArg;
        RAST._IType _out34;
        _out34 = (this).GenType(_1067_typeArg, false, false);
        _1069_rTypeArg = _out34;
        _1055_fields = Dafny.Sequence<RAST._IField>.Concat(_1055_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1066_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1069_rTypeArg))))));
        _1056_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1056_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1066_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1070_datatypeName;
      _1070_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1071_struct;
      _1071_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1070_datatypeName, _1052_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1055_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1071_struct));
      Dafny.ISequence<RAST._IImplMember> _1072_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1073_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out36;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _1050_typeParamsSet, out _out35, out _out36);
      _1072_implBodyRaw = _out35;
      _1073_traitBodies = _out36;
      Dafny.ISequence<RAST._IImplMember> _1074_implBody;
      _1074_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_1070_datatypeName), _1056_fieldInits))))), _1072_implBodyRaw);
      RAST._IImpl _1075_i;
      _1075_i = RAST.Impl.create_Impl(_1052_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1070_datatypeName), _1051_rTypeParams), _1053_whereConstraints, _1074_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1075_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1076_i;
        _1076_i = BigInteger.Zero;
        while ((_1076_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1077_superClass;
          _1077_superClass = ((c).dtor_superClasses).Select(_1076_i);
          DAST._IType _source46 = _1077_superClass;
          bool unmatched46 = true;
          if (unmatched46) {
            if (_source46.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1078_traitPath = _source46.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _1079_typeArgs = _source46.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source46.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1080___v41 = resolved0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1081___v42 = resolved0.dtor_attributes;
                unmatched46 = false;
                {
                  RAST._IType _1082_pathStr;
                  RAST._IType _out37;
                  _out37 = DCOMP.COMP.GenPath(_1078_traitPath);
                  _1082_pathStr = _out37;
                  Dafny.ISequence<RAST._IType> _1083_typeArgs;
                  Dafny.ISequence<RAST._IType> _out38;
                  _out38 = (this).GenTypeArgs(_1079_typeArgs, false, false);
                  _1083_typeArgs = _out38;
                  Dafny.ISequence<RAST._IImplMember> _1084_body;
                  _1084_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1073_traitBodies).Contains(_1078_traitPath)) {
                    _1084_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1073_traitBodies,_1078_traitPath);
                  }
                  RAST._IType _1085_genSelfPath;
                  RAST._IType _out39;
                  _out39 = DCOMP.COMP.GenPath(path);
                  _1085_genSelfPath = _out39;
                  RAST._IModDecl _1086_x;
                  _1086_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1052_rTypeParamsDecls, RAST.Type.create_TypeApp(_1082_pathStr, _1083_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_1085_genSelfPath, _1051_rTypeParams)), _1053_whereConstraints, _1084_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1086_x));
                }
              }
            }
          }
          if (unmatched46) {
            DAST._IType _1087___v43 = _source46;
            unmatched46 = false;
          }
          _1076_i = (_1076_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1088_d;
      _1088_d = RAST.Impl.create_ImplFor(_1052_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1070_datatypeName), _1051_rTypeParams), _1053_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_1070_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1089_defaultImpl;
      _1089_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1088_d));
      RAST._IImpl _1090_p;
      _1090_p = RAST.Impl.create_ImplFor(_1052_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1070_datatypeName), _1051_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1091_printImpl;
      _1091_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1090_p));
      RAST._IImpl _1092_pp;
      _1092_pp = RAST.Impl.create_ImplFor(_1052_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1070_datatypeName), _1051_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1093_ptrPartialEqImpl;
      _1093_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1092_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1089_defaultImpl), _1091_printImpl), _1093_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1094_typeParamsSet;
      _1094_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1095_typeParamDecls;
      _1095_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1096_typeParams;
      _1096_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1097_tpI;
      _1097_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1097_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _1098_tp;
          _1098_tp = ((t).dtor_typeParams).Select(_1097_tpI);
          DAST._IType _1099_typeArg;
          RAST._ITypeParamDecl _1100_typeParamDecl;
          DAST._IType _out40;
          RAST._ITypeParamDecl _out41;
          (this).GenTypeParam(_1098_tp, out _out40, out _out41);
          _1099_typeArg = _out40;
          _1100_typeParamDecl = _out41;
          _1094_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1094_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1099_typeArg));
          _1095_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1095_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1100_typeParamDecl));
          RAST._IType _1101_typeParam;
          RAST._IType _out42;
          _out42 = (this).GenType(_1099_typeArg, false, false);
          _1101_typeParam = _out42;
          _1096_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1096_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1101_typeParam));
          _1097_tpI = (_1097_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1102_fullPath;
      _1102_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1103_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1104___v44;
      Dafny.ISequence<RAST._IImplMember> _out43;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out44;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1102_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1102_fullPath, (t).dtor_attributes)), _1094_typeParamsSet, out _out43, out _out44);
      _1103_implBody = _out43;
      _1104___v44 = _out44;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1095_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1096_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1103_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1105_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1106_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1107_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1108_whereConstraints;
      Dafny.ISet<DAST._IType> _out45;
      Dafny.ISequence<RAST._IType> _out46;
      Dafny.ISequence<RAST._ITypeParamDecl> _out47;
      Dafny.ISequence<Dafny.Rune> _out48;
      (this).GenTypeParameters((c).dtor_typeParams, out _out45, out _out46, out _out47, out _out48);
      _1105_typeParamsSet = _out45;
      _1106_rTypeParams = _out46;
      _1107_rTypeParamsDecls = _out47;
      _1108_whereConstraints = _out48;
      Dafny.ISequence<Dafny.Rune> _1109_constrainedTypeParams;
      _1109_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1107_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1110_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source47 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched47 = true;
      if (unmatched47) {
        if (_source47.is_Some) {
          RAST._IType _1111_v = _source47.dtor_value;
          unmatched47 = false;
          _1110_underlyingType = _1111_v;
        }
      }
      if (unmatched47) {
        unmatched47 = false;
        RAST._IType _out49;
        _out49 = (this).GenType((c).dtor_base, false, false);
        _1110_underlyingType = _out49;
      }
      DAST._IType _1112_resultingType;
      _1112_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _1113_datatypeName;
      _1113_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1113_datatypeName, _1107_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1110_underlyingType))))));
      RAST._IExpr _1114_fnBody;
      _1114_fnBody = RAST.Expr.create_Identifier(_1113_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source48 = (c).dtor_witnessExpr;
      bool unmatched48 = true;
      if (unmatched48) {
        if (_source48.is_Some) {
          DAST._IExpression _1115_e = _source48.dtor_value;
          unmatched48 = false;
          {
            DAST._IExpression _1116_e;
            _1116_e = ((object.Equals((c).dtor_base, _1112_resultingType)) ? (_1115_e) : (DAST.Expression.create_Convert(_1115_e, (c).dtor_base, _1112_resultingType)));
            RAST._IExpr _1117_eStr;
            DCOMP._IOwnership _1118___v45;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1119___v46;
            RAST._IExpr _out50;
            DCOMP._IOwnership _out51;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
            (this).GenExpr(_1116_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
            _1117_eStr = _out50;
            _1118___v45 = _out51;
            _1119___v46 = _out52;
            _1114_fnBody = (_1114_fnBody).Apply1(_1117_eStr);
          }
        }
      }
      if (unmatched48) {
        unmatched48 = false;
        {
          _1114_fnBody = (_1114_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1120_body;
      _1120_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1114_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1107_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1113_datatypeName), _1106_rTypeParams), _1108_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1120_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1107_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1113_datatypeName), _1106_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1107_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1113_datatypeName), _1106_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1110_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1121_typeParamsSet;
      Dafny.ISequence<RAST._IType> _1122_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1123_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1124_whereConstraints;
      Dafny.ISet<DAST._IType> _out53;
      Dafny.ISequence<RAST._IType> _out54;
      Dafny.ISequence<RAST._ITypeParamDecl> _out55;
      Dafny.ISequence<Dafny.Rune> _out56;
      (this).GenTypeParameters((c).dtor_typeParams, out _out53, out _out54, out _out55, out _out56);
      _1121_typeParamsSet = _out53;
      _1122_rTypeParams = _out54;
      _1123_rTypeParamsDecls = _out55;
      _1124_whereConstraints = _out56;
      Dafny.ISequence<Dafny.Rune> _1125_datatypeName;
      _1125_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1126_ctors;
      _1126_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1127_i = BigInteger.Zero; _1127_i < _hi9; _1127_i++) {
        DAST._IDatatypeCtor _1128_ctor;
        _1128_ctor = ((c).dtor_ctors).Select(_1127_i);
        Dafny.ISequence<RAST._IField> _1129_ctorArgs;
        _1129_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        BigInteger _hi10 = new BigInteger(((_1128_ctor).dtor_args).Count);
        for (BigInteger _1130_j = BigInteger.Zero; _1130_j < _hi10; _1130_j++) {
          DAST._IFormal _1131_formal;
          _1131_formal = ((_1128_ctor).dtor_args).Select(_1130_j);
          RAST._IType _1132_formalType;
          RAST._IType _out57;
          _out57 = (this).GenType((_1131_formal).dtor_typ, false, false);
          _1132_formalType = _out57;
          if ((c).dtor_isCo) {
            _1129_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1129_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_1131_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1132_formalType))))));
          } else {
            _1129_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1129_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_1131_formal).dtor_name), _1132_formalType))));
          }
        }
        _1126_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1126_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1128_ctor).dtor_name), RAST.Fields.create_NamedFields(_1129_ctorArgs))));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1133_selfPath;
      _1133_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1134_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1135_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out58;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out59;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_1133_selfPath, (c).dtor_attributes))), _1121_typeParamsSet, out _out58, out _out59);
      _1134_implBodyRaw = _out58;
      _1135_traitBodies = _out59;
      Dafny.ISequence<RAST._IImplMember> _1136_implBody;
      _1136_implBody = _1134_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1137_emittedFields;
      _1137_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1138_i = BigInteger.Zero; _1138_i < _hi11; _1138_i++) {
        DAST._IDatatypeCtor _1139_ctor;
        _1139_ctor = ((c).dtor_ctors).Select(_1138_i);
        BigInteger _hi12 = new BigInteger(((_1139_ctor).dtor_args).Count);
        for (BigInteger _1140_j = BigInteger.Zero; _1140_j < _hi12; _1140_j++) {
          DAST._IFormal _1141_formal;
          _1141_formal = ((_1139_ctor).dtor_args).Select(_1140_j);
          if (!((_1137_emittedFields).Contains((_1141_formal).dtor_name))) {
            _1137_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1137_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1141_formal).dtor_name));
            RAST._IType _1142_formalType;
            RAST._IType _out60;
            _out60 = (this).GenType((_1141_formal).dtor_typ, false, false);
            _1142_formalType = _out60;
            Dafny.ISequence<RAST._IMatchCase> _1143_cases;
            _1143_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1144_k = BigInteger.Zero; _1144_k < _hi13; _1144_k++) {
              DAST._IDatatypeCtor _1145_ctor2;
              _1145_ctor2 = ((c).dtor_ctors).Select(_1144_k);
              Dafny.ISequence<Dafny.Rune> _1146_pattern;
              _1146_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1125_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1145_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _1147_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              bool _1148_hasMatchingField;
              _1148_hasMatchingField = false;
              BigInteger _hi14 = new BigInteger(((_1145_ctor2).dtor_args).Count);
              for (BigInteger _1149_l = BigInteger.Zero; _1149_l < _hi14; _1149_l++) {
                DAST._IFormal _1150_formal2;
                _1150_formal2 = ((_1145_ctor2).dtor_args).Select(_1149_l);
                if (object.Equals((_1141_formal).dtor_name, (_1150_formal2).dtor_name)) {
                  _1148_hasMatchingField = true;
                }
                _1146_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1146_pattern, DCOMP.__default.escapeName((_1150_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1146_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_1146_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_1148_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _1147_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeName((_1141_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1147_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_1141_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1147_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1151_ctorMatch;
              _1151_ctorMatch = RAST.MatchCase.create(_1146_pattern, RAST.Expr.create_RawExpr(_1147_rhs));
              _1143_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1143_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1151_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1143_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1143_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1125_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1152_methodBody;
            _1152_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1143_cases);
            _1136_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1136_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeName((_1141_formal).dtor_name), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1142_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1152_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1153_types;
        _1153_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1154_typeI = BigInteger.Zero; _1154_typeI < _hi15; _1154_typeI++) {
          DAST._IType _1155_typeArg;
          RAST._ITypeParamDecl _1156_rTypeParamDecl;
          DAST._IType _out61;
          RAST._ITypeParamDecl _out62;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1154_typeI), out _out61, out _out62);
          _1155_typeArg = _out61;
          _1156_rTypeParamDecl = _out62;
          RAST._IType _1157_rTypeArg;
          RAST._IType _out63;
          _out63 = (this).GenType(_1155_typeArg, false, false);
          _1157_rTypeArg = _out63;
          _1153_types = Dafny.Sequence<RAST._IType>.Concat(_1153_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1157_rTypeArg))));
        }
        _1126_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1126_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1158_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1158_tpe);
})), _1153_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1159_enumBody;
      _1159_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1125_datatypeName, _1123_rTypeParamsDecls, _1126_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1123_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1122_rTypeParams), _1124_whereConstraints, _1136_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1160_printImplBodyCases;
      _1160_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1161_i = BigInteger.Zero; _1161_i < _hi16; _1161_i++) {
        DAST._IDatatypeCtor _1162_ctor;
        _1162_ctor = ((c).dtor_ctors).Select(_1161_i);
        Dafny.ISequence<Dafny.Rune> _1163_ctorMatch;
        _1163_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_1162_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _1164_modulePrefix;
        _1164_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName(((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1165_ctorName;
        _1165_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1164_modulePrefix, DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((_1162_ctor).dtor_name));
        if (((new BigInteger((_1165_ctorName).Count)) >= (new BigInteger(13))) && (((_1165_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1165_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1166_printRhs;
        _1166_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1165_ctorName), (((_1162_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _hi17 = new BigInteger(((_1162_ctor).dtor_args).Count);
        for (BigInteger _1167_j = BigInteger.Zero; _1167_j < _hi17; _1167_j++) {
          DAST._IFormal _1168_formal;
          _1168_formal = ((_1162_ctor).dtor_args).Select(_1167_j);
          Dafny.ISequence<Dafny.Rune> _1169_formalName;
          _1169_formalName = DCOMP.__default.escapeName((_1168_formal).dtor_name);
          _1163_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1163_ctorMatch, _1169_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1167_j).Sign == 1) {
            _1166_printRhs = (_1166_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1166_printRhs = (_1166_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeName((_1168_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        _1163_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_1163_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_1162_ctor).dtor_hasAnyArgs) {
          _1166_printRhs = (_1166_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1166_printRhs = (_1166_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1160_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1160_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1125_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1163_ctorMatch), RAST.Expr.create_Block(_1166_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1160_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1160_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1125_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1170_defaultConstrainedTypeParams;
      _1170_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1123_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _1171_printImplBody;
      _1171_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1160_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1172_printImpl;
      _1172_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1123_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1122_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1123_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1122_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1171_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1173_defaultImpl;
      _1173_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1174_structName;
        _1174_structName = (RAST.Expr.create_Identifier(_1125_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1175_structAssignments;
        _1175_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1176_i = BigInteger.Zero; _1176_i < _hi18; _1176_i++) {
          DAST._IFormal _1177_formal;
          _1177_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1176_i);
          _1175_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1175_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName((_1177_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1178_defaultConstrainedTypeParams;
        _1178_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1123_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1179_fullType;
        _1179_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1125_datatypeName), _1122_rTypeParams);
        _1173_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1179_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1179_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1174_structName, _1175_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1159_enumBody, _1172_printImpl), _1173_defaultImpl);
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
        for (BigInteger _1180_i = BigInteger.Zero; _1180_i < _hi19; _1180_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1180_i))));
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
        for (BigInteger _1181_i = BigInteger.Zero; _1181_i < _hi20; _1181_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1181_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1182_i;
        _1182_i = BigInteger.Zero;
        while ((_1182_i) < (new BigInteger((args).Count))) {
          RAST._IType _1183_genTp;
          RAST._IType _out64;
          _out64 = (this).GenType((args).Select(_1182_i), inBinding, inFn);
          _1183_genTp = _out64;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1183_genTp));
          _1182_i = (_1182_i) + (BigInteger.One);
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
      DAST._IType _source49 = c;
      bool unmatched49 = true;
      if (unmatched49) {
        if (_source49.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1184_p = _source49.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _1185_args = _source49.dtor_typeArgs;
          DAST._IResolvedType _1186_resolved = _source49.dtor_resolved;
          unmatched49 = false;
          {
            RAST._IType _1187_t;
            RAST._IType _out65;
            _out65 = DCOMP.COMP.GenPath(_1184_p);
            _1187_t = _out65;
            Dafny.ISequence<RAST._IType> _1188_typeArgs;
            Dafny.ISequence<RAST._IType> _out66;
            _out66 = (this).GenTypeArgs(_1185_args, inBinding, inFn);
            _1188_typeArgs = _out66;
            s = RAST.Type.create_TypeApp(_1187_t, _1188_typeArgs);
            DAST._IResolvedType _source50 = _1186_resolved;
            bool unmatched50 = true;
            if (unmatched50) {
              if (_source50.is_Datatype) {
                DAST._IDatatypeType datatypeType0 = _source50.dtor_datatypeType;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1189___v47 = datatypeType0.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1190_attributes = datatypeType0.dtor_attributes;
                unmatched50 = false;
                {
                  if ((this).IsRcWrapped(_1190_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched50) {
              if (_source50.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1191___v48 = _source50.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _1192___v49 = _source50.dtor_attributes;
                unmatched50 = false;
                {
                  if ((_1184_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            if (unmatched50) {
              DAST._IType _1193_t = _source50.dtor_baseType;
              DAST._INewtypeRange _1194_range = _source50.dtor_range;
              bool _1195_erased = _source50.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1196_attributes = _source50.dtor_attributes;
              unmatched50 = false;
              {
                if (_1195_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source51 = DCOMP.COMP.NewtypeToRustType(_1193_t, _1194_range);
                  bool unmatched51 = true;
                  if (unmatched51) {
                    if (_source51.is_Some) {
                      RAST._IType _1197_v = _source51.dtor_value;
                      unmatched51 = false;
                      s = _1197_v;
                    }
                  }
                  if (unmatched51) {
                    unmatched51 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Nullable) {
          DAST._IType _1198_inner = _source49.dtor_Nullable_a0;
          unmatched49 = false;
          {
            RAST._IType _1199_innerExpr;
            RAST._IType _out67;
            _out67 = (this).GenType(_1198_inner, inBinding, inFn);
            _1199_innerExpr = _out67;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1199_innerExpr));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1200_types = _source49.dtor_Tuple_a0;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1201_args;
            _1201_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1202_i;
            _1202_i = BigInteger.Zero;
            while ((_1202_i) < (new BigInteger((_1200_types).Count))) {
              RAST._IType _1203_generated;
              RAST._IType _out68;
              _out68 = (this).GenType((_1200_types).Select(_1202_i), inBinding, inFn);
              _1203_generated = _out68;
              _1201_args = Dafny.Sequence<RAST._IType>.Concat(_1201_args, Dafny.Sequence<RAST._IType>.FromElements(_1203_generated));
              _1202_i = (_1202_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1200_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1201_args)) : (RAST.__default.SystemTupleType(_1201_args)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Array) {
          DAST._IType _1204_element = _source49.dtor_element;
          BigInteger _1205_dims = _source49.dtor_dims;
          unmatched49 = false;
          {
            RAST._IType _1206_elem;
            RAST._IType _out69;
            _out69 = (this).GenType(_1204_element, inBinding, inFn);
            _1206_elem = _out69;
            s = _1206_elem;
            BigInteger _1207_i;
            _1207_i = BigInteger.Zero;
            while ((_1207_i) < (_1205_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1207_i = (_1207_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Seq) {
          DAST._IType _1208_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1209_elem;
            RAST._IType _out70;
            _out70 = (this).GenType(_1208_element, inBinding, inFn);
            _1209_elem = _out70;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1209_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Set) {
          DAST._IType _1210_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1211_elem;
            RAST._IType _out71;
            _out71 = (this).GenType(_1210_element, inBinding, inFn);
            _1211_elem = _out71;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1211_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Multiset) {
          DAST._IType _1212_element = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1213_elem;
            RAST._IType _out72;
            _out72 = (this).GenType(_1212_element, inBinding, inFn);
            _1213_elem = _out72;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1213_elem));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Map) {
          DAST._IType _1214_key = _source49.dtor_key;
          DAST._IType _1215_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1216_keyType;
            RAST._IType _out73;
            _out73 = (this).GenType(_1214_key, inBinding, inFn);
            _1216_keyType = _out73;
            RAST._IType _1217_valueType;
            RAST._IType _out74;
            _out74 = (this).GenType(_1215_value, inBinding, inFn);
            _1217_valueType = _out74;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1216_keyType, _1217_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_MapBuilder) {
          DAST._IType _1218_key = _source49.dtor_key;
          DAST._IType _1219_value = _source49.dtor_value;
          unmatched49 = false;
          {
            RAST._IType _1220_keyType;
            RAST._IType _out75;
            _out75 = (this).GenType(_1218_key, inBinding, inFn);
            _1220_keyType = _out75;
            RAST._IType _1221_valueType;
            RAST._IType _out76;
            _out76 = (this).GenType(_1219_value, inBinding, inFn);
            _1221_valueType = _out76;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1220_keyType, _1221_valueType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_SetBuilder) {
          DAST._IType _1222_elem = _source49.dtor_element;
          unmatched49 = false;
          {
            RAST._IType _1223_elemType;
            RAST._IType _out77;
            _out77 = (this).GenType(_1222_elem, inBinding, inFn);
            _1223_elemType = _out77;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1223_elemType));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1224_args = _source49.dtor_args;
          DAST._IType _1225_result = _source49.dtor_result;
          unmatched49 = false;
          {
            Dafny.ISequence<RAST._IType> _1226_argTypes;
            _1226_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1227_i;
            _1227_i = BigInteger.Zero;
            while ((_1227_i) < (new BigInteger((_1224_args).Count))) {
              RAST._IType _1228_generated;
              RAST._IType _out78;
              _out78 = (this).GenType((_1224_args).Select(_1227_i), inBinding, true);
              _1228_generated = _out78;
              _1226_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1226_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1228_generated)));
              _1227_i = (_1227_i) + (BigInteger.One);
            }
            RAST._IType _1229_resultType;
            RAST._IType _out79;
            _out79 = (this).GenType(_1225_result, inBinding, (inFn) || (inBinding));
            _1229_resultType = _out79;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1226_argTypes, _1229_resultType)));
          }
        }
      }
      if (unmatched49) {
        if (_source49.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h100 = _source49.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1230_name = _h100;
          unmatched49 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1230_name));
        }
      }
      if (unmatched49) {
        if (_source49.is_Primitive) {
          DAST._IPrimitive _1231_p = _source49.dtor_Primitive_a0;
          unmatched49 = false;
          {
            DAST._IPrimitive _source52 = _1231_p;
            bool unmatched52 = true;
            if (unmatched52) {
              if (_source52.is_Int) {
                unmatched52 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched52) {
              if (_source52.is_Real) {
                unmatched52 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched52) {
              if (_source52.is_String) {
                unmatched52 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched52) {
              if (_source52.is_Bool) {
                unmatched52 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched52) {
              unmatched52 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched49) {
        Dafny.ISequence<Dafny.Rune> _1232_v = _source49.dtor_Passthrough_a0;
        unmatched49 = false;
        s = RAST.__default.RawType(_1232_v);
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
      for (BigInteger _1233_i = BigInteger.Zero; _1233_i < _hi21; _1233_i++) {
        DAST._IMethod _source53 = (body).Select(_1233_i);
        bool unmatched53 = true;
        if (unmatched53) {
          DAST._IMethod _1234_m = _source53;
          unmatched53 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source54 = (_1234_m).dtor_overridingPath;
            bool unmatched54 = true;
            if (unmatched54) {
              if (_source54.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1235_p = _source54.dtor_value;
                unmatched54 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1236_existing;
                  _1236_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1235_p)) {
                    _1236_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1235_p);
                  }
                  RAST._IImplMember _1237_genMethod;
                  RAST._IImplMember _out80;
                  _out80 = (this).GenMethod(_1234_m, true, enclosingType, enclosingTypeParams);
                  _1237_genMethod = _out80;
                  _1236_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1236_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1237_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1235_p, _1236_existing)));
                }
              }
            }
            if (unmatched54) {
              unmatched54 = false;
              {
                RAST._IImplMember _1238_generated;
                RAST._IImplMember _out81;
                _out81 = (this).GenMethod(_1234_m, forTrait, enclosingType, enclosingTypeParams);
                _1238_generated = _out81;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1238_generated));
              }
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
      for (BigInteger _1239_i = BigInteger.Zero; _1239_i < _hi22; _1239_i++) {
        DAST._IFormal _1240_param;
        _1240_param = (@params).Select(_1239_i);
        RAST._IType _1241_paramType;
        RAST._IType _out82;
        _out82 = (this).GenType((_1240_param).dtor_typ, false, false);
        _1241_paramType = _out82;
        if ((!((_1241_paramType).CanReadWithoutClone())) && (!((_1240_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1241_paramType = RAST.Type.create_Borrowed(_1241_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1240_param).dtor_name), _1241_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1242_params;
      Dafny.ISequence<RAST._IFormal> _out83;
      _out83 = (this).GenParams((m).dtor_params);
      _1242_params = _out83;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1243_paramNames;
      _1243_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1244_paramTypes;
      _1244_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1245_paramI = BigInteger.Zero; _1245_paramI < _hi23; _1245_paramI++) {
        DAST._IFormal _1246_dafny__formal;
        _1246_dafny__formal = ((m).dtor_params).Select(_1245_paramI);
        RAST._IFormal _1247_formal;
        _1247_formal = (_1242_params).Select(_1245_paramI);
        Dafny.ISequence<Dafny.Rune> _1248_name;
        _1248_name = (_1247_formal).dtor_name;
        _1243_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1243_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1248_name));
        _1244_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1244_paramTypes, _1248_name, (_1247_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1249_fnName;
      _1249_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1250_selfIdentifier;
      _1250_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1251_selfId;
        _1251_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1249_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1251_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _1252_selfFormal;
          _1252_selfFormal = RAST.Formal.selfBorrowedMut;
          _1242_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1252_selfFormal), _1242_params);
        } else {
          RAST._IType _1253_tpe;
          RAST._IType _out84;
          _out84 = (this).GenType(enclosingType, false, false);
          _1253_tpe = _out84;
          if (!((_1253_tpe).CanReadWithoutClone())) {
            _1253_tpe = RAST.Type.create_Borrowed(_1253_tpe);
          }
          _1242_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1251_selfId, _1253_tpe)), _1242_params);
        }
        _1250_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1251_selfId);
      }
      Dafny.ISequence<RAST._IType> _1254_retTypeArgs;
      _1254_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1255_typeI;
      _1255_typeI = BigInteger.Zero;
      while ((_1255_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1256_typeExpr;
        RAST._IType _out85;
        _out85 = (this).GenType(((m).dtor_outTypes).Select(_1255_typeI), false, false);
        _1256_typeExpr = _out85;
        _1254_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1254_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1256_typeExpr));
        _1255_typeI = (_1255_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1257_visibility;
      _1257_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _1258_typeParamsFiltered;
      _1258_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1259_typeParamI = BigInteger.Zero; _1259_typeParamI < _hi24; _1259_typeParamI++) {
        DAST._ITypeArgDecl _1260_typeParam;
        _1260_typeParam = ((m).dtor_typeParams).Select(_1259_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1260_typeParam).dtor_name)))) {
          _1258_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1258_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1260_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1261_typeParams;
      _1261_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1258_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_1258_typeParamsFiltered).Count);
        for (BigInteger _1262_i = BigInteger.Zero; _1262_i < _hi25; _1262_i++) {
          DAST._IType _1263_typeArg;
          RAST._ITypeParamDecl _1264_rTypeParamDecl;
          DAST._IType _out86;
          RAST._ITypeParamDecl _out87;
          (this).GenTypeParam((_1258_typeParamsFiltered).Select(_1262_i), out _out86, out _out87);
          _1263_typeArg = _out86;
          _1264_rTypeParamDecl = _out87;
          _1261_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1261_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1264_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1265_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1266_env = DCOMP.Environment.Default();
      RAST._IExpr _1267_preBody;
      _1267_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _1268_earlyReturn;
        _1268_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source55 = (m).dtor_outVars;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1269_outVars = _source55.dtor_value;
            unmatched55 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1270_tupleArgs;
              _1270_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi26 = new BigInteger((_1269_outVars).Count);
              for (BigInteger _1271_outI = BigInteger.Zero; _1271_outI < _hi26; _1271_outI++) {
                Dafny.ISequence<Dafny.Rune> _1272_outVar;
                _1272_outVar = (_1269_outVars).Select(_1271_outI);
                RAST._IType _1273_outType;
                RAST._IType _out88;
                _out88 = (this).GenType(((m).dtor_outTypes).Select(_1271_outI), false, false);
                _1273_outType = _out88;
                Dafny.ISequence<Dafny.Rune> _1274_outName;
                _1274_outName = DCOMP.__default.escapeName((_1272_outVar));
                _1243_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1243_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1274_outName));
                RAST._IType _1275_outMaybeType;
                _1275_outMaybeType = (((_1273_outType).CanReadWithoutClone()) ? (_1273_outType) : (RAST.Type.create_Borrowed(_1273_outType)));
                _1244_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1244_paramTypes, _1274_outName, _1275_outMaybeType);
                RAST._IExpr _1276_outVarReturn;
                DCOMP._IOwnership _1277___v50;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1278___v51;
                RAST._IExpr _out89;
                DCOMP._IOwnership _out90;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
                (this).GenExpr(DAST.Expression.create_Ident((_1272_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1274_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1274_outName, _1275_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
                _1276_outVarReturn = _out89;
                _1277___v50 = _out90;
                _1278___v51 = _out91;
                _1270_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1270_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1276_outVarReturn));
              }
              if ((new BigInteger((_1270_tupleArgs).Count)) == (BigInteger.One)) {
                _1268_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1270_tupleArgs).Select(BigInteger.Zero)));
              } else {
                _1268_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1270_tupleArgs)));
              }
            }
          }
        }
        if (unmatched55) {
          unmatched55 = false;
        }
        _1266_env = DCOMP.Environment.create(_1243_paramNames, _1244_paramTypes);
        RAST._IExpr _1279_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1280___v52;
        DCOMP._IEnvironment _1281___v53;
        RAST._IExpr _out92;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
        DCOMP._IEnvironment _out94;
        (this).GenStmts((m).dtor_body, _1250_selfIdentifier, _1266_env, true, _1268_earlyReturn, out _out92, out _out93, out _out94);
        _1279_body = _out92;
        _1280___v52 = _out93;
        _1281___v53 = _out94;
        _1265_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1267_preBody).Then(_1279_body));
      } else {
        _1266_env = DCOMP.Environment.create(_1243_paramNames, _1244_paramTypes);
        _1265_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1257_visibility, RAST.Fn.create(_1249_fnName, _1261_typeParams, _1242_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1254_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1254_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1254_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1265_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1282_declarations;
      _1282_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1283_i;
      _1283_i = BigInteger.Zero;
      newEnv = env;
      while ((_1283_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1284_stmt;
        _1284_stmt = (stmts).Select(_1283_i);
        RAST._IExpr _1285_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1286_recIdents;
        DCOMP._IEnvironment _1287_newEnv2;
        RAST._IExpr _out95;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
        DCOMP._IEnvironment _out97;
        (this).GenStmt(_1284_stmt, selfIdent, newEnv, (isLast) && ((_1283_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out95, out _out96, out _out97);
        _1285_stmtExpr = _out95;
        _1286_recIdents = _out96;
        _1287_newEnv2 = _out97;
        newEnv = _1287_newEnv2;
        DAST._IStatement _source56 = _1284_stmt;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1288_name = _source56.dtor_name;
            DAST._IType _1289___v54 = _source56.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1290___v55 = _source56.dtor_maybeValue;
            unmatched56 = false;
            {
              _1282_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1282_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1288_name)));
            }
          }
        }
        if (unmatched56) {
          DAST._IStatement _1291___v56 = _source56;
          unmatched56 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1286_recIdents, _1282_declarations));
        generated = (generated).Then(_1285_stmtExpr);
        _1283_i = (_1283_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source57 = lhs;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident0 = _source57.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1292_id = ident0;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1293_idRust;
            _1293_idRust = DCOMP.__default.escapeName(_1292_id);
            if (((env).IsBorrowed(_1293_idRust)) || ((env).IsBorrowedMut(_1293_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1293_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1293_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1293_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Select) {
          DAST._IExpression _1294_on = _source57.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1295_field = _source57.dtor_field;
          unmatched57 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1296_fieldName;
            _1296_fieldName = DCOMP.__default.escapeName(_1295_field);
            RAST._IExpr _1297_onExpr;
            DCOMP._IOwnership _1298_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1299_recIdents;
            RAST._IExpr _out98;
            DCOMP._IOwnership _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            (this).GenExpr(_1294_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out98, out _out99, out _out100);
            _1297_onExpr = _out98;
            _1298_onOwned = _out99;
            _1299_recIdents = _out100;
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1297_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1296_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
            readIdents = _1299_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched57) {
        DAST._IExpression _1300_on = _source57.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1301_indices = _source57.dtor_indices;
        unmatched57 = false;
        {
          RAST._IExpr _1302_onExpr;
          DCOMP._IOwnership _1303_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1304_recIdents;
          RAST._IExpr _out101;
          DCOMP._IOwnership _out102;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
          (this).GenExpr(_1300_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
          _1302_onExpr = _out101;
          _1303_onOwned = _out102;
          _1304_recIdents = _out103;
          readIdents = _1304_recIdents;
          Dafny.ISequence<Dafny.Rune> _1305_r;
          _1305_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1306_i;
          _1306_i = BigInteger.Zero;
          while ((_1306_i) < (new BigInteger((_1301_indices).Count))) {
            RAST._IExpr _1307_idx;
            DCOMP._IOwnership _1308___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1309_recIdentsIdx;
            RAST._IExpr _out104;
            DCOMP._IOwnership _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            (this).GenExpr((_1301_indices).Select(_1306_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out104, out _out105, out _out106);
            _1307_idx = _out104;
            _1308___v57 = _out105;
            _1309_recIdentsIdx = _out106;
            _1305_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1305_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1306_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1307_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1309_recIdentsIdx);
            _1306_i = (_1306_i) + (BigInteger.One);
          }
          _1305_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1305_r, (_1302_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1306_i = BigInteger.Zero;
          while ((_1306_i) < (new BigInteger((_1301_indices).Count))) {
            _1305_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1305_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1306_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1306_i = (_1306_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1305_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source58 = stmt;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1310_name = _source58.dtor_name;
          DAST._IType _1311_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source58.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1312_expression = maybeValue0.dtor_value;
            unmatched58 = false;
            {
              RAST._IType _1313_tpe;
              RAST._IType _out107;
              _out107 = (this).GenType(_1311_typ, true, false);
              _1313_tpe = _out107;
              RAST._IExpr _1314_expr;
              DCOMP._IOwnership _1315_exprOwnership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1316_recIdents;
              RAST._IExpr _out108;
              DCOMP._IOwnership _out109;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
              (this).GenExpr(_1312_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out108, out _out109, out _out110);
              _1314_expr = _out108;
              _1315_exprOwnership = _out109;
              _1316_recIdents = _out110;
              readIdents = _1316_recIdents;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1310_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1313_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1314_expr));
              newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1310_name), _1313_tpe);
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1317_name = _source58.dtor_name;
          DAST._IType _1318_typ = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source58.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched58 = false;
            {
              DAST._IStatement _1319_newStmt;
              _1319_newStmt = DAST.Statement.create_DeclareVar(_1317_name, _1318_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1318_typ)));
              RAST._IExpr _out111;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
              DCOMP._IEnvironment _out113;
              (this).GenStmt(_1319_newStmt, selfIdent, env, isLast, earlyReturn, out _out111, out _out112, out _out113);
              generated = _out111;
              readIdents = _out112;
              newEnv = _out113;
            }
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Assign) {
          DAST._IAssignLhs _1320_lhs = _source58.dtor_lhs;
          DAST._IExpression _1321_expression = _source58.dtor_value;
          unmatched58 = false;
          {
            RAST._IExpr _1322_exprGen;
            DCOMP._IOwnership _1323___v58;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1324_exprIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1321_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
            _1322_exprGen = _out114;
            _1323___v58 = _out115;
            _1324_exprIdents = _out116;
            if ((_1320_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1325_rustId;
              _1325_rustId = DCOMP.__default.escapeName(((_1320_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1326_tpe;
              _1326_tpe = (env).GetType(_1325_rustId);
            }
            RAST._IExpr _1327_lhsGen;
            bool _1328_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1329_recIdents;
            DCOMP._IEnvironment _1330_resEnv;
            RAST._IExpr _out117;
            bool _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            DCOMP._IEnvironment _out120;
            (this).GenAssignLhs(_1320_lhs, _1322_exprGen, selfIdent, env, out _out117, out _out118, out _out119, out _out120);
            _1327_lhsGen = _out117;
            _1328_needsIIFE = _out118;
            _1329_recIdents = _out119;
            _1330_resEnv = _out120;
            generated = _1327_lhsGen;
            newEnv = _1330_resEnv;
            if (_1328_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1329_recIdents, _1324_exprIdents);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_If) {
          DAST._IExpression _1331_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1332_thnDafny = _source58.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1333_elsDafny = _source58.dtor_els;
          unmatched58 = false;
          {
            RAST._IExpr _1334_cond;
            DCOMP._IOwnership _1335___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1336_recIdents;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr(_1331_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1334_cond = _out121;
            _1335___v59 = _out122;
            _1336_recIdents = _out123;
            Dafny.ISequence<Dafny.Rune> _1337_condString;
            _1337_condString = (_1334_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1336_recIdents;
            RAST._IExpr _1338_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1339_thnIdents;
            DCOMP._IEnvironment _1340_thnEnv;
            RAST._IExpr _out124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
            DCOMP._IEnvironment _out126;
            (this).GenStmts(_1332_thnDafny, selfIdent, env, isLast, earlyReturn, out _out124, out _out125, out _out126);
            _1338_thn = _out124;
            _1339_thnIdents = _out125;
            _1340_thnEnv = _out126;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1339_thnIdents);
            RAST._IExpr _1341_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_elsIdents;
            DCOMP._IEnvironment _1343_elsEnv;
            RAST._IExpr _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            DCOMP._IEnvironment _out129;
            (this).GenStmts(_1333_elsDafny, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
            _1341_els = _out127;
            _1342_elsIdents = _out128;
            _1343_elsEnv = _out129;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1342_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1334_cond, _1338_thn, _1341_els);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1344_lbl = _source58.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1345_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1346_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1347_bodyIdents;
            DCOMP._IEnvironment _1348_env2;
            RAST._IExpr _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            DCOMP._IEnvironment _out132;
            (this).GenStmts(_1345_body, selfIdent, env, isLast, earlyReturn, out _out130, out _out131, out _out132);
            _1346_body = _out130;
            _1347_bodyIdents = _out131;
            _1348_env2 = _out132;
            readIdents = _1347_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1344_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1346_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_While) {
          DAST._IExpression _1349_cond = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1350_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1351_cond;
            DCOMP._IOwnership _1352___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1353_recIdents;
            RAST._IExpr _out133;
            DCOMP._IOwnership _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            (this).GenExpr(_1349_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
            _1351_cond = _out133;
            _1352___v60 = _out134;
            _1353_recIdents = _out135;
            readIdents = _1353_recIdents;
            RAST._IExpr _1354_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1355_bodyIdents;
            DCOMP._IEnvironment _1356_bodyEnv;
            RAST._IExpr _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            DCOMP._IEnvironment _out138;
            (this).GenStmts(_1350_body, selfIdent, env, false, earlyReturn, out _out136, out _out137, out _out138);
            _1354_bodyExpr = _out136;
            _1355_bodyIdents = _out137;
            _1356_bodyEnv = _out138;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1355_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1351_cond), _1354_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1357_boundName = _source58.dtor_boundName;
          DAST._IType _1358_boundType = _source58.dtor_boundType;
          DAST._IExpression _1359_over = _source58.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1360_body = _source58.dtor_body;
          unmatched58 = false;
          {
            RAST._IExpr _1361_over;
            DCOMP._IOwnership _1362___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1363_recIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1359_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1361_over = _out139;
            _1362___v61 = _out140;
            _1363_recIdents = _out141;
            RAST._IType _1364_boundTpe;
            RAST._IType _out142;
            _out142 = (this).GenType(_1358_boundType, false, false);
            _1364_boundTpe = _out142;
            readIdents = _1363_recIdents;
            Dafny.ISequence<Dafny.Rune> _1365_boundRName;
            _1365_boundRName = DCOMP.__default.escapeName(_1357_boundName);
            RAST._IExpr _1366_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1367_bodyIdents;
            DCOMP._IEnvironment _1368_bodyEnv;
            RAST._IExpr _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenStmts(_1360_body, selfIdent, (env).AddAssigned(_1365_boundRName, _1364_boundTpe), false, earlyReturn, out _out143, out _out144, out _out145);
            _1366_bodyExpr = _out143;
            _1367_bodyIdents = _out144;
            _1368_bodyEnv = _out145;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1367_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1365_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1365_boundRName, _1361_over, _1366_bodyExpr);
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1369_toLabel = _source58.dtor_toLabel;
          unmatched58 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source59 = _1369_toLabel;
            bool unmatched59 = true;
            if (unmatched59) {
              if (_source59.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1370_lbl = _source59.dtor_value;
                unmatched59 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1370_lbl)));
                }
              }
            }
            if (unmatched59) {
              unmatched59 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1371_body = _source58.dtor_body;
          unmatched58 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
            }
            newEnv = env;
            BigInteger _hi27 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1372_paramI = BigInteger.Zero; _1372_paramI < _hi27; _1372_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1373_param;
              _1373_param = ((env).dtor_names).Select(_1372_paramI);
              RAST._IExpr _1374_paramInit;
              DCOMP._IOwnership _1375___v62;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1376___v63;
              RAST._IExpr _out146;
              DCOMP._IOwnership _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              (this).GenIdent(_1373_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
              _1374_paramInit = _out146;
              _1375___v62 = _out147;
              _1376___v63 = _out148;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1373_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1374_paramInit)));
              if (((env).dtor_types).Contains(_1373_param)) {
                RAST._IType _1377_declaredType;
                _1377_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1373_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1373_param, _1377_declaredType);
              }
            }
            RAST._IExpr _1378_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1379_bodyIdents;
            DCOMP._IEnvironment _1380_bodyEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1371_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out149, out _out150, out _out151);
            _1378_bodyExpr = _out149;
            _1379_bodyIdents = _out150;
            _1380_bodyEnv = _out151;
            readIdents = _1379_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1378_bodyExpr)));
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_JumpTailCallStart) {
          unmatched58 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Call) {
          DAST._IExpression _1381_on = _source58.dtor_on;
          DAST._ICallName _1382_name = _source58.dtor_callName;
          Dafny.ISequence<DAST._IType> _1383_typeArgs = _source58.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1384_args = _source58.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1385_maybeOutVars = _source58.dtor_outs;
          unmatched58 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1386_onExpr;
            DCOMP._IOwnership _1387___v64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1388_enclosingIdents;
            RAST._IExpr _out152;
            DCOMP._IOwnership _out153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out154;
            (this).GenExpr(_1381_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out152, out _out153, out _out154);
            _1386_onExpr = _out152;
            _1387___v64 = _out153;
            _1388_enclosingIdents = _out154;
            Dafny.ISequence<RAST._IType> _1389_typeArgsR;
            _1389_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1383_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1390_typeI;
              _1390_typeI = BigInteger.Zero;
              while ((_1390_typeI) < (new BigInteger((_1383_typeArgs).Count))) {
                RAST._IType _1391_tpe;
                RAST._IType _out155;
                _out155 = (this).GenType((_1383_typeArgs).Select(_1390_typeI), false, false);
                _1391_tpe = _out155;
                _1389_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1389_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1391_tpe));
                _1390_typeI = (_1390_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1392_argExprs;
            _1392_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi28 = new BigInteger((_1384_args).Count);
            for (BigInteger _1393_i = BigInteger.Zero; _1393_i < _hi28; _1393_i++) {
              DCOMP._IOwnership _1394_argOwnership;
              _1394_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1382_name).is_CallName) && ((_1393_i) < (new BigInteger((((_1382_name).dtor_signature)).Count)))) {
                RAST._IType _1395_tpe;
                RAST._IType _out156;
                _out156 = (this).GenType(((((_1382_name).dtor_signature)).Select(_1393_i)).dtor_typ, false, false);
                _1395_tpe = _out156;
                if ((_1395_tpe).CanReadWithoutClone()) {
                  _1394_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1396_argExpr;
              DCOMP._IOwnership _1397_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1398_argIdents;
              RAST._IExpr _out157;
              DCOMP._IOwnership _out158;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
              (this).GenExpr((_1384_args).Select(_1393_i), selfIdent, env, _1394_argOwnership, out _out157, out _out158, out _out159);
              _1396_argExpr = _out157;
              _1397_ownership = _out158;
              _1398_argIdents = _out159;
              _1392_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1392_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1396_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1398_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1388_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1399_renderedName;
            _1399_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source60 = _1382_name;
              bool unmatched60 = true;
              if (unmatched60) {
                if (_source60.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1400_name = _source60.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1401___v65 = _source60.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1402___v66 = _source60.dtor_signature;
                  unmatched60 = false;
                  return DCOMP.__default.escapeName(_1400_name);
                }
              }
              if (unmatched60) {
                bool disjunctiveMatch9 = false;
                if (_source60.is_MapBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (_source60.is_SetBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (disjunctiveMatch9) {
                  unmatched60 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched60) {
                bool disjunctiveMatch10 = false;
                disjunctiveMatch10 = true;
                disjunctiveMatch10 = true;
                if (disjunctiveMatch10) {
                  unmatched60 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source61 = _1381_on;
            bool unmatched61 = true;
            if (unmatched61) {
              if (_source61.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1403___v67 = _source61.dtor_Companion_a0;
                unmatched61 = false;
                {
                  _1386_onExpr = (_1386_onExpr).MSel(_1399_renderedName);
                }
              }
            }
            if (unmatched61) {
              DAST._IExpression _1404___v68 = _source61;
              unmatched61 = false;
              {
                _1386_onExpr = (_1386_onExpr).Sel(_1399_renderedName);
              }
            }
            generated = _1386_onExpr;
            if ((new BigInteger((_1389_typeArgsR).Count)).Sign == 1) {
              generated = (generated).ApplyType(_1389_typeArgsR);
            }
            generated = (generated).Apply(_1392_argExprs);
            if (((_1385_maybeOutVars).is_Some) && ((new BigInteger(((_1385_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1405_outVar;
              _1405_outVar = DCOMP.__default.escapeName((((_1385_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              generated = RAST.__default.AssignVar(_1405_outVar, generated);
            } else if (((_1385_maybeOutVars).is_None) || ((new BigInteger(((_1385_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1406_tmpVar;
              _1406_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1407_tmpId;
              _1407_tmpId = RAST.Expr.create_Identifier(_1406_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1406_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1408_outVars;
              _1408_outVars = (_1385_maybeOutVars).dtor_value;
              BigInteger _hi29 = new BigInteger((_1408_outVars).Count);
              for (BigInteger _1409_outI = BigInteger.Zero; _1409_outI < _hi29; _1409_outI++) {
                Dafny.ISequence<Dafny.Rune> _1410_outVar;
                _1410_outVar = DCOMP.__default.escapeName(((_1408_outVars).Select(_1409_outI)));
                RAST._IExpr _1411_rhs;
                _1411_rhs = (_1407_tmpId).Sel(Std.Strings.__default.OfNat(_1409_outI));
                generated = (generated).Then(RAST.__default.AssignVar(_1410_outVar, _1411_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Return) {
          DAST._IExpression _1412_exprDafny = _source58.dtor_expr;
          unmatched58 = false;
          {
            RAST._IExpr _1413_expr;
            DCOMP._IOwnership _1414___v69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1415_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1412_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1413_expr = _out160;
            _1414___v69 = _out161;
            _1415_recIdents = _out162;
            readIdents = _1415_recIdents;
            if (isLast) {
              generated = _1413_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1413_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_EarlyReturn) {
          unmatched58 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        if (_source58.is_Halt) {
          unmatched58 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched58) {
        DAST._IExpression _1416_e = _source58.dtor_Print_a0;
        unmatched58 = false;
        {
          RAST._IExpr _1417_printedExpr;
          DCOMP._IOwnership _1418_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419_recIdents;
          RAST._IExpr _out163;
          DCOMP._IOwnership _out164;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
          (this).GenExpr(_1416_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out163, out _out164, out _out165);
          _1417_printedExpr = _out163;
          _1418_recOwnership = _out164;
          _1419_recIdents = _out165;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1417_printedExpr)));
          readIdents = _1419_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source62 = range;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_NoRange) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched62) {
        if (_source62.is_U8) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched62) {
        if (_source62.is_U16) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched62) {
        if (_source62.is_U32) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched62) {
        if (_source62.is_U64) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched62) {
        if (_source62.is_U128) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched62) {
        if (_source62.is_I8) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched62) {
        if (_source62.is_I16) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched62) {
        if (_source62.is_I32) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched62) {
        if (_source62.is_I64) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched62) {
        if (_source62.is_I128) {
          unmatched62 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched62) {
        DAST._INewtypeRange _1420___v70 = _source62;
        unmatched62 = false;
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      throw new System.Exception("unexpected control point");
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
      DAST._IExpression _source63 = e;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h140 = _source63.dtor_Literal_a0;
          if (_h140.is_BoolLiteral) {
            bool _1421_b = _h140.dtor_BoolLiteral_a0;
            unmatched63 = false;
            {
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_1421_b), expectedOwnership, out _out170, out _out171);
              r = _out170;
              resultingOwnership = _out171;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h141 = _source63.dtor_Literal_a0;
          if (_h141.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1422_i = _h141.dtor_IntLiteral_a0;
            DAST._IType _1423_t = _h141.dtor_IntLiteral_a1;
            unmatched63 = false;
            {
              DAST._IType _source64 = _1423_t;
              bool unmatched64 = true;
              if (unmatched64) {
                if (_source64.is_Primitive) {
                  DAST._IPrimitive _h80 = _source64.dtor_Primitive_a0;
                  if (_h80.is_Int) {
                    unmatched64 = false;
                    {
                      if ((new BigInteger((_1422_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1422_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1422_i, true));
                      }
                    }
                  }
                }
              }
              if (unmatched64) {
                DAST._IType _1424_o = _source64;
                unmatched64 = false;
                {
                  RAST._IType _1425_genType;
                  RAST._IType _out172;
                  _out172 = (this).GenType(_1424_o, false, false);
                  _1425_genType = _out172;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1422_i), _1425_genType);
                }
              }
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out173, out _out174);
              r = _out173;
              resultingOwnership = _out174;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h142 = _source63.dtor_Literal_a0;
          if (_h142.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1426_n = _h142.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1427_d = _h142.dtor_DecLiteral_a1;
            DAST._IType _1428_t = _h142.dtor_DecLiteral_a2;
            unmatched63 = false;
            {
              DAST._IType _source65 = _1428_t;
              bool unmatched65 = true;
              if (unmatched65) {
                if (_source65.is_Primitive) {
                  DAST._IPrimitive _h81 = _source65.dtor_Primitive_a0;
                  if (_h81.is_Real) {
                    unmatched65 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1426_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1427_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched65) {
                DAST._IType _1429_o = _source65;
                unmatched65 = false;
                {
                  RAST._IType _1430_genType;
                  RAST._IType _out175;
                  _out175 = (this).GenType(_1429_o, false, false);
                  _1430_genType = _out175;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1426_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1427_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1430_genType);
                }
              }
              RAST._IExpr _out176;
              DCOMP._IOwnership _out177;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out176, out _out177);
              r = _out176;
              resultingOwnership = _out177;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h143 = _source63.dtor_Literal_a0;
          if (_h143.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1431_l = _h143.dtor_StringLiteral_a0;
            unmatched63 = false;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1431_l, false));
              RAST._IExpr _out178;
              DCOMP._IOwnership _out179;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
              r = _out178;
              resultingOwnership = _out179;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Literal) {
          DAST._ILiteral _h144 = _source63.dtor_Literal_a0;
          if (_h144.is_CharLiteral) {
            Dafny.Rune _1432_c = _h144.dtor_CharLiteral_a0;
            unmatched63 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1432_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out180;
              DCOMP._IOwnership _out181;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out180, out _out181);
              r = _out180;
              resultingOwnership = _out181;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched63) {
        DAST._ILiteral _h145 = _source63.dtor_Literal_a0;
        DAST._IType _1433_tpe = _h145.dtor_Null_a0;
        unmatched63 = false;
        {
          RAST._IType _1434_tpeGen;
          RAST._IType _out182;
          _out182 = (this).GenType(_1433_tpe, false, false);
          _1434_tpeGen = _out182;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1434_tpeGen);
          RAST._IExpr _out183;
          DCOMP._IOwnership _out184;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out183, out _out184);
          r = _out183;
          resultingOwnership = _out184;
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
      DAST._IBinOp _1435_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _1436_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _1437_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _1438_format = _let_tmp_rhs52.dtor_format2;
      bool _1439_becomesLeftCallsRight;
      _1439_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source66 = _1435_op;
        bool unmatched66 = true;
        if (unmatched66) {
          bool disjunctiveMatch11 = false;
          if (_source66.is_SetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_SetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MapMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MapSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_MultisetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source66.is_Concat) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            unmatched66 = false;
            return true;
          }
        }
        if (unmatched66) {
          DAST._IBinOp _1440___v71 = _source66;
          unmatched66 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1441_becomesRightCallsLeft;
      _1441_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source67 = _1435_op;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_In) {
            unmatched67 = false;
            return true;
          }
        }
        if (unmatched67) {
          DAST._IBinOp _1442___v72 = _source67;
          unmatched67 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1443_becomesCallLeftRight;
      _1443_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source68 = _1435_op;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Eq) {
            bool referential0 = _source68.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source68.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched68 = false;
                return true;
              }
            }
          }
        }
        if (unmatched68) {
          if (_source68.is_SetMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetIntersection) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_SetDisjoint) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MapMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MapSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetMerge) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetSubtraction) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetIntersection) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_MultisetDisjoint) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          if (_source68.is_Concat) {
            unmatched68 = false;
            return true;
          }
        }
        if (unmatched68) {
          DAST._IBinOp _1444___v73 = _source68;
          unmatched68 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1445_expectedLeftOwnership;
      _1445_expectedLeftOwnership = ((_1439_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1441_becomesRightCallsLeft) || (_1443_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1446_expectedRightOwnership;
      _1446_expectedRightOwnership = (((_1439_becomesLeftCallsRight) || (_1443_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1441_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1447_left;
      DCOMP._IOwnership _1448___v74;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1449_recIdentsL;
      RAST._IExpr _out185;
      DCOMP._IOwnership _out186;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
      (this).GenExpr(_1436_lExpr, selfIdent, env, _1445_expectedLeftOwnership, out _out185, out _out186, out _out187);
      _1447_left = _out185;
      _1448___v74 = _out186;
      _1449_recIdentsL = _out187;
      RAST._IExpr _1450_right;
      DCOMP._IOwnership _1451___v75;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1452_recIdentsR;
      RAST._IExpr _out188;
      DCOMP._IOwnership _out189;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
      (this).GenExpr(_1437_rExpr, selfIdent, env, _1446_expectedRightOwnership, out _out188, out _out189, out _out190);
      _1450_right = _out188;
      _1451___v75 = _out189;
      _1452_recIdentsR = _out190;
      DAST._IBinOp _source69 = _1435_op;
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_In) {
          unmatched69 = false;
          {
            r = ((_1450_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1447_left);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqProperPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1447_left, _1450_right, _1438_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SeqPrefix) {
          unmatched69 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1447_left, _1450_right, _1438_format);
        }
      }
      if (unmatched69) {
        if (_source69.is_SetMerge) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetIntersection) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Subset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1447_left, _1450_right, _1438_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1447_left, _1450_right, _1438_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_SetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapMerge) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MapSubtraction) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetMerge) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetSubtraction) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetIntersection) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Submultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1447_left, _1450_right, _1438_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_ProperSubmultiset) {
          unmatched69 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1447_left, _1450_right, _1438_format);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_MultisetDisjoint) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Concat) {
          unmatched69 = false;
          {
            r = ((_1447_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1450_right);
          }
        }
      }
      if (unmatched69) {
        DAST._IBinOp _1453___v76 = _source69;
        unmatched69 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1435_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1435_op), _1447_left, _1450_right, _1438_format);
          } else {
            DAST._IBinOp _source70 = _1435_op;
            bool unmatched70 = true;
            if (unmatched70) {
              if (_source70.is_Eq) {
                bool _1454_referential = _source70.dtor_referential;
                bool _1455_nullable = _source70.dtor_nullable;
                unmatched70 = false;
                {
                  if (_1454_referential) {
                    if (_1455_nullable) {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1447_left, _1450_right));
                    } else {
                      r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1447_left, _1450_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1447_left, _1450_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianDiv) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1447_left, _1450_right));
                }
              }
            }
            if (unmatched70) {
              if (_source70.is_EuclidianMod) {
                unmatched70 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1447_left, _1450_right));
                }
              }
            }
            if (unmatched70) {
              Dafny.ISequence<Dafny.Rune> _1456_op = _source70.dtor_Passthrough_a0;
              unmatched70 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1456_op, _1447_left, _1450_right, _1438_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out191;
      DCOMP._IOwnership _out192;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out191, out _out192);
      r = _out191;
      resultingOwnership = _out192;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1449_recIdentsL, _1452_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _1457_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _1458_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _1459_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _1460_recursiveGen;
      DCOMP._IOwnership _1461_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1462_recIdents;
      RAST._IExpr _out193;
      DCOMP._IOwnership _out194;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out195;
      (this).GenExpr(_1457_expr, selfIdent, env, expectedOwnership, out _out193, out _out194, out _out195);
      _1460_recursiveGen = _out193;
      _1461_recOwned = _out194;
      _1462_recIdents = _out195;
      r = _1460_recursiveGen;
      if (object.Equals(_1461_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out196;
      DCOMP._IOwnership _out197;
      DCOMP.COMP.FromOwnership(r, _1461_recOwned, expectedOwnership, out _out196, out _out197);
      r = _out196;
      resultingOwnership = _out197;
      readIdents = _1462_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1463_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1464_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1465_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _1466_recursiveGen;
      DCOMP._IOwnership _1467_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1468_recIdents;
      RAST._IExpr _out198;
      DCOMP._IOwnership _out199;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
      (this).GenExpr(_1463_expr, selfIdent, env, expectedOwnership, out _out198, out _out199, out _out200);
      _1466_recursiveGen = _out198;
      _1467_recOwned = _out199;
      _1468_recIdents = _out200;
      r = _1466_recursiveGen;
      if (object.Equals(_1467_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out201;
      DCOMP._IOwnership _out202;
      DCOMP.COMP.FromOwnership(r, _1467_recOwned, expectedOwnership, out _out201, out _out202);
      r = _out201;
      resultingOwnership = _out202;
      readIdents = _1468_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1469_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1470_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1471_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1471_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1472___v77 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1473___v78 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1474_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1475_range = _let_tmp_rhs57.dtor_range;
      bool _1476_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1477_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1478_nativeToType;
      _1478_nativeToType = DCOMP.COMP.NewtypeToRustType(_1474_b, _1475_range);
      if (object.Equals(_1470_fromTpe, _1474_b)) {
        RAST._IExpr _1479_recursiveGen;
        DCOMP._IOwnership _1480_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1481_recIdents;
        RAST._IExpr _out203;
        DCOMP._IOwnership _out204;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
        (this).GenExpr(_1469_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out203, out _out204, out _out205);
        _1479_recursiveGen = _out203;
        _1480_recOwned = _out204;
        _1481_recIdents = _out205;
        readIdents = _1481_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source71 = _1478_nativeToType;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_Some) {
            RAST._IType _1482_v = _source71.dtor_value;
            unmatched71 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1479_recursiveGen, RAST.Expr.create_ExprFromType(_1482_v)));
            RAST._IExpr _out206;
            DCOMP._IOwnership _out207;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out206, out _out207);
            r = _out206;
            resultingOwnership = _out207;
          }
        }
        if (unmatched71) {
          unmatched71 = false;
          if (_1476_erase) {
            r = _1479_recursiveGen;
          } else {
            RAST._IType _1483_rhsType;
            RAST._IType _out208;
            _out208 = (this).GenType(_1471_toTpe, true, false);
            _1483_rhsType = _out208;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1483_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1479_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out209;
          DCOMP._IOwnership _out210;
          DCOMP.COMP.FromOwnership(r, _1480_recOwned, expectedOwnership, out _out209, out _out210);
          r = _out209;
          resultingOwnership = _out210;
        }
      } else {
        RAST._IExpr _out211;
        DCOMP._IOwnership _out212;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1469_expr, _1470_fromTpe, _1474_b), _1474_b, _1471_toTpe), selfIdent, env, expectedOwnership, out _out211, out _out212, out _out213);
        r = _out211;
        resultingOwnership = _out212;
        readIdents = _out213;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1484_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1485_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1486_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1485_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1487___v79 = _let_tmp_rhs59.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _1488___v80 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _1489_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1490_range = _let_tmp_rhs60.dtor_range;
      bool _1491_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1492_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _1493_nativeFromType;
      _1493_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1489_b, _1490_range);
      if (object.Equals(_1489_b, _1486_toTpe)) {
        RAST._IExpr _1494_recursiveGen;
        DCOMP._IOwnership _1495_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_recIdents;
        RAST._IExpr _out214;
        DCOMP._IOwnership _out215;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out216;
        (this).GenExpr(_1484_expr, selfIdent, env, expectedOwnership, out _out214, out _out215, out _out216);
        _1494_recursiveGen = _out214;
        _1495_recOwned = _out215;
        _1496_recIdents = _out216;
        readIdents = _1496_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source72 = _1493_nativeFromType;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_Some) {
            RAST._IType _1497_v = _source72.dtor_value;
            unmatched72 = false;
            RAST._IType _1498_toTpeRust;
            RAST._IType _out217;
            _out217 = (this).GenType(_1486_toTpe, false, false);
            _1498_toTpeRust = _out217;
            r = (((_1494_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1498_toTpeRust))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out218;
            DCOMP._IOwnership _out219;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out218, out _out219);
            r = _out218;
            resultingOwnership = _out219;
          }
        }
        if (unmatched72) {
          unmatched72 = false;
          if (_1491_erase) {
            r = _1494_recursiveGen;
          } else {
            r = (_1494_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          DCOMP.COMP.FromOwnership(r, _1495_recOwned, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
        }
      } else {
        if ((_1493_nativeFromType).is_Some) {
          if (object.Equals(_1486_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1499_recursiveGen;
            DCOMP._IOwnership _1500_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1501_recIdents;
            RAST._IExpr _out222;
            DCOMP._IOwnership _out223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
            (this).GenExpr(_1484_expr, selfIdent, env, expectedOwnership, out _out222, out _out223, out _out224);
            _1499_recursiveGen = _out222;
            _1500_recOwned = _out223;
            _1501_recIdents = _out224;
            RAST._IExpr _out225;
            DCOMP._IOwnership _out226;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1499_recursiveGen, (this).DafnyCharUnderlying)), _1500_recOwned, expectedOwnership, out _out225, out _out226);
            r = _out225;
            resultingOwnership = _out226;
            readIdents = _1501_recIdents;
            return ;
          }
        }
        RAST._IExpr _out227;
        DCOMP._IOwnership _out228;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out229;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1484_expr, _1485_fromTpe, _1489_b), _1489_b, _1486_toTpe), selfIdent, env, expectedOwnership, out _out227, out _out228, out _out229);
        r = _out227;
        resultingOwnership = _out228;
        readIdents = _out229;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1502_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1503_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1504_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _1505_fromTpeGen;
      RAST._IType _out230;
      _out230 = (this).GenType(_1503_fromTpe, true, false);
      _1505_fromTpeGen = _out230;
      RAST._IType _1506_toTpeGen;
      RAST._IType _out231;
      _out231 = (this).GenType(_1504_toTpe, true, false);
      _1506_toTpeGen = _out231;
      RAST._IExpr _1507_recursiveGen;
      DCOMP._IOwnership _1508_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1509_recIdents;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
      (this).GenExpr(_1502_expr, selfIdent, env, expectedOwnership, out _out232, out _out233, out _out234);
      _1507_recursiveGen = _out232;
      _1508_recOwned = _out233;
      _1509_recIdents = _out234;
      Dafny.ISequence<Dafny.Rune> _1510_msg;
      _1510_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1505_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1506_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1510_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1507_recursiveGen)._ToString(DCOMP.__default.IND), _1510_msg));
      RAST._IExpr _out235;
      DCOMP._IOwnership _out236;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out235, out _out236);
      r = _out235;
      resultingOwnership = _out236;
      readIdents = _1509_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1511_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1512_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1513_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_1512_fromTpe, _1513_toTpe)) {
        RAST._IExpr _1514_recursiveGen;
        DCOMP._IOwnership _1515_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1516_recIdents;
        RAST._IExpr _out237;
        DCOMP._IOwnership _out238;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
        (this).GenExpr(_1511_expr, selfIdent, env, expectedOwnership, out _out237, out _out238, out _out239);
        _1514_recursiveGen = _out237;
        _1515_recOwned = _out238;
        _1516_recIdents = _out239;
        r = _1514_recursiveGen;
        RAST._IExpr _out240;
        DCOMP._IOwnership _out241;
        DCOMP.COMP.FromOwnership(r, _1515_recOwned, expectedOwnership, out _out240, out _out241);
        r = _out240;
        resultingOwnership = _out241;
        readIdents = _1516_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source73 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1512_fromTpe, _1513_toTpe);
        bool unmatched73 = true;
        if (unmatched73) {
          DAST._IType _01 = _source73.dtor__0;
          if (_01.is_Nullable) {
            DAST._IType _1517___v81 = _01.dtor_Nullable_a0;
            DAST._IType _1518___v82 = _source73.dtor__1;
            unmatched73 = false;
            {
              RAST._IExpr _out242;
              DCOMP._IOwnership _out243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out242, out _out243, out _out244);
              r = _out242;
              resultingOwnership = _out243;
              readIdents = _out244;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1519___v83 = _source73.dtor__0;
          DAST._IType _11 = _source73.dtor__1;
          if (_11.is_Nullable) {
            DAST._IType _1520___v84 = _11.dtor_Nullable_a0;
            unmatched73 = false;
            {
              RAST._IExpr _out245;
              DCOMP._IOwnership _out246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out245, out _out246, out _out247);
              r = _out245;
              resultingOwnership = _out246;
              readIdents = _out247;
            }
          }
        }
        if (unmatched73) {
          DAST._IType _1521___v85 = _source73.dtor__0;
          DAST._IType _12 = _source73.dtor__1;
          if (_12.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1522___v86 = _12.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1523___v87 = _12.dtor_typeArgs;
            DAST._IResolvedType resolved1 = _12.dtor_resolved;
            if (resolved1.is_Newtype) {
              DAST._IType _1524_b = resolved1.dtor_baseType;
              DAST._INewtypeRange _1525_range = resolved1.dtor_range;
              bool _1526_erase = resolved1.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1527_attributes = resolved1.dtor_attributes;
              unmatched73 = false;
              {
                RAST._IExpr _out248;
                DCOMP._IOwnership _out249;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
                r = _out248;
                resultingOwnership = _out249;
                readIdents = _out250;
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _02 = _source73.dtor__0;
          if (_02.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1528___v88 = _02.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1529___v89 = _02.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _02.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1530_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1531_range = resolved2.dtor_range;
              bool _1532_erase = resolved2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1533_attributes = resolved2.dtor_attributes;
              DAST._IType _1534___v90 = _source73.dtor__1;
              unmatched73 = false;
              {
                RAST._IExpr _out251;
                DCOMP._IOwnership _out252;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
                r = _out251;
                resultingOwnership = _out252;
                readIdents = _out253;
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _03 = _source73.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h82 = _03.dtor_Primitive_a0;
            if (_h82.is_Int) {
              DAST._IType _13 = _source73.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h83 = _13.dtor_Primitive_a0;
                if (_h83.is_Real) {
                  unmatched73 = false;
                  {
                    RAST._IExpr _1535_recursiveGen;
                    DCOMP._IOwnership _1536___v91;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1537_recIdents;
                    RAST._IExpr _out254;
                    DCOMP._IOwnership _out255;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
                    (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out254, out _out255, out _out256);
                    _1535_recursiveGen = _out254;
                    _1536___v91 = _out255;
                    _1537_recIdents = _out256;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1535_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out257;
                    DCOMP._IOwnership _out258;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out257, out _out258);
                    r = _out257;
                    resultingOwnership = _out258;
                    readIdents = _1537_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _04 = _source73.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h84 = _04.dtor_Primitive_a0;
            if (_h84.is_Real) {
              DAST._IType _14 = _source73.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h85 = _14.dtor_Primitive_a0;
                if (_h85.is_Int) {
                  unmatched73 = false;
                  {
                    RAST._IExpr _1538_recursiveGen;
                    DCOMP._IOwnership _1539___v92;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1540_recIdents;
                    RAST._IExpr _out259;
                    DCOMP._IOwnership _out260;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
                    (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out259, out _out260, out _out261);
                    _1538_recursiveGen = _out259;
                    _1539___v92 = _out260;
                    _1540_recIdents = _out261;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1538_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out262;
                    DCOMP._IOwnership _out263;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out262, out _out263);
                    r = _out262;
                    resultingOwnership = _out263;
                    readIdents = _1540_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _05 = _source73.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h86 = _05.dtor_Primitive_a0;
            if (_h86.is_Int) {
              DAST._IType _15 = _source73.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1541___v93 = _15.dtor_Passthrough_a0;
                unmatched73 = false;
                {
                  RAST._IType _1542_rhsType;
                  RAST._IType _out264;
                  _out264 = (this).GenType(_1513_toTpe, true, false);
                  _1542_rhsType = _out264;
                  RAST._IExpr _1543_recursiveGen;
                  DCOMP._IOwnership _1544___v94;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1545_recIdents;
                  RAST._IExpr _out265;
                  DCOMP._IOwnership _out266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
                  (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out265, out _out266, out _out267);
                  _1543_recursiveGen = _out265;
                  _1544___v94 = _out266;
                  _1545_recIdents = _out267;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1542_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1543_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out268;
                  DCOMP._IOwnership _out269;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out268, out _out269);
                  r = _out268;
                  resultingOwnership = _out269;
                  readIdents = _1545_recIdents;
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _06 = _source73.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1546___v95 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source73.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h87 = _16.dtor_Primitive_a0;
              if (_h87.is_Int) {
                unmatched73 = false;
                {
                  RAST._IType _1547_rhsType;
                  RAST._IType _out270;
                  _out270 = (this).GenType(_1512_fromTpe, true, false);
                  _1547_rhsType = _out270;
                  RAST._IExpr _1548_recursiveGen;
                  DCOMP._IOwnership _1549___v96;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1550_recIdents;
                  RAST._IExpr _out271;
                  DCOMP._IOwnership _out272;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out273;
                  (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out271, out _out272, out _out273);
                  _1548_recursiveGen = _out271;
                  _1549___v96 = _out272;
                  _1550_recIdents = _out273;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1548_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out274;
                  DCOMP._IOwnership _out275;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out274, out _out275);
                  r = _out274;
                  resultingOwnership = _out275;
                  readIdents = _1550_recIdents;
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _07 = _source73.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h88 = _07.dtor_Primitive_a0;
            if (_h88.is_Int) {
              DAST._IType _17 = _source73.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h89 = _17.dtor_Primitive_a0;
                if (_h89.is_Char) {
                  unmatched73 = false;
                  {
                    RAST._IType _1551_rhsType;
                    RAST._IType _out276;
                    _out276 = (this).GenType(_1513_toTpe, true, false);
                    _1551_rhsType = _out276;
                    RAST._IExpr _1552_recursiveGen;
                    DCOMP._IOwnership _1553___v97;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
                    RAST._IExpr _out277;
                    DCOMP._IOwnership _out278;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
                    (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out277, out _out278, out _out279);
                    _1552_recursiveGen = _out277;
                    _1553___v97 = _out278;
                    _1554_recIdents = _out279;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1552_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out280;
                    DCOMP._IOwnership _out281;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out280, out _out281);
                    r = _out280;
                    resultingOwnership = _out281;
                    readIdents = _1554_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _08 = _source73.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h810 = _08.dtor_Primitive_a0;
            if (_h810.is_Char) {
              DAST._IType _18 = _source73.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h811 = _18.dtor_Primitive_a0;
                if (_h811.is_Int) {
                  unmatched73 = false;
                  {
                    RAST._IType _1555_rhsType;
                    RAST._IType _out282;
                    _out282 = (this).GenType(_1512_fromTpe, true, false);
                    _1555_rhsType = _out282;
                    RAST._IExpr _1556_recursiveGen;
                    DCOMP._IOwnership _1557___v98;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1558_recIdents;
                    RAST._IExpr _out283;
                    DCOMP._IOwnership _out284;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                    (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out283, out _out284, out _out285);
                    _1556_recursiveGen = _out283;
                    _1557___v98 = _out284;
                    _1558_recIdents = _out285;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1556_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out286, out _out287);
                    r = _out286;
                    resultingOwnership = _out287;
                    readIdents = _1558_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched73) {
          DAST._IType _09 = _source73.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1559___v99 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source73.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1560___v100 = _19.dtor_Passthrough_a0;
              unmatched73 = false;
              {
                RAST._IExpr _1561_recursiveGen;
                DCOMP._IOwnership _1562___v101;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1563_recIdents;
                RAST._IExpr _out288;
                DCOMP._IOwnership _out289;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                (this).GenExpr(_1511_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out288, out _out289, out _out290);
                _1561_recursiveGen = _out288;
                _1562___v101 = _out289;
                _1563_recIdents = _out290;
                RAST._IType _1564_toTpeGen;
                RAST._IType _out291;
                _out291 = (this).GenType(_1513_toTpe, true, false);
                _1564_toTpeGen = _out291;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1561_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1564_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out292, out _out293);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _1563_recIdents;
              }
            }
          }
        }
        if (unmatched73) {
          _System._ITuple2<DAST._IType, DAST._IType> _1565___v102 = _source73;
          unmatched73 = false;
          {
            RAST._IExpr _out294;
            DCOMP._IOwnership _out295;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out296;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out294, out _out295, out _out296);
            r = _out294;
            resultingOwnership = _out295;
            readIdents = _out296;
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
      Std.Wrappers._IOption<RAST._IType> _1566_tpe;
      _1566_tpe = (env).GetType(rName);
      bool _1567_currentlyBorrowed;
      _1567_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1568_noNeedOfClone;
      _1568_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_1568_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1568_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1567_currentlyBorrowed) {
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
      DAST._IExpression _source74 = e;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_Literal) {
          DAST._ILiteral _1569___v103 = _source74.dtor_Literal_a0;
          unmatched74 = false;
          RAST._IExpr _out297;
          DCOMP._IOwnership _out298;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out297, out _out298, out _out299);
          r = _out297;
          resultingOwnership = _out298;
          readIdents = _out299;
        }
      }
      if (unmatched74) {
        if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1570_name = _source74.dtor_Ident_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out300;
            DCOMP._IOwnership _out301;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
            (this).GenIdent(DCOMP.__default.escapeName(_1570_name), selfIdent, env, expectedOwnership, out _out300, out _out301, out _out302);
            r = _out300;
            resultingOwnership = _out301;
            readIdents = _out302;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1571_path = _source74.dtor_Companion_a0;
          unmatched74 = false;
          {
            RAST._IExpr _out303;
            _out303 = DCOMP.COMP.GenPathExpr(_1571_path);
            r = _out303;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out304;
              DCOMP._IOwnership _out305;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out304, out _out305);
              r = _out304;
              resultingOwnership = _out305;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_InitializationValue) {
          DAST._IType _1572_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IType _1573_typExpr;
            RAST._IType _out306;
            _out306 = (this).GenType(_1572_typ, false, false);
            _1573_typExpr = _out306;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1573_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            RAST._IExpr _out307;
            DCOMP._IOwnership _out308;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out307, out _out308);
            r = _out307;
            resultingOwnership = _out308;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1574_values = _source74.dtor_Tuple_a0;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1575_exprs;
            _1575_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi30 = new BigInteger((_1574_values).Count);
            for (BigInteger _1576_i = BigInteger.Zero; _1576_i < _hi30; _1576_i++) {
              RAST._IExpr _1577_recursiveGen;
              DCOMP._IOwnership _1578___v104;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1579_recIdents;
              RAST._IExpr _out309;
              DCOMP._IOwnership _out310;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
              (this).GenExpr((_1574_values).Select(_1576_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
              _1577_recursiveGen = _out309;
              _1578___v104 = _out310;
              _1579_recIdents = _out311;
              _1575_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1575_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1577_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1579_recIdents);
            }
            r = (((new BigInteger((_1574_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1575_exprs)) : (RAST.__default.SystemTuple(_1575_exprs)));
            RAST._IExpr _out312;
            DCOMP._IOwnership _out313;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out312, out _out313);
            r = _out312;
            resultingOwnership = _out313;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1580_path = _source74.dtor_path;
          Dafny.ISequence<DAST._IType> _1581_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1582_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _out314;
            _out314 = DCOMP.COMP.GenPathExpr(_1580_path);
            r = _out314;
            if ((new BigInteger((_1581_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1583_typeExprs;
              _1583_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi31 = new BigInteger((_1581_typeArgs).Count);
              for (BigInteger _1584_i = BigInteger.Zero; _1584_i < _hi31; _1584_i++) {
                RAST._IType _1585_typeExpr;
                RAST._IType _out315;
                _out315 = (this).GenType((_1581_typeArgs).Select(_1584_i), false, false);
                _1585_typeExpr = _out315;
                _1583_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1583_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1585_typeExpr));
              }
              r = (r).ApplyType(_1583_typeExprs);
            }
            r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_allocated"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1586_arguments;
            _1586_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi32 = new BigInteger((_1582_args).Count);
            for (BigInteger _1587_i = BigInteger.Zero; _1587_i < _hi32; _1587_i++) {
              RAST._IExpr _1588_recursiveGen;
              DCOMP._IOwnership _1589___v105;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_recIdents;
              RAST._IExpr _out316;
              DCOMP._IOwnership _out317;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
              (this).GenExpr((_1582_args).Select(_1587_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
              _1588_recursiveGen = _out316;
              _1589___v105 = _out317;
              _1590_recIdents = _out318;
              _1586_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1586_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1588_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1590_recIdents);
            }
            r = (r).Apply(_1586_arguments);
            RAST._IExpr _out319;
            DCOMP._IOwnership _out320;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out319, out _out320);
            r = _out319;
            resultingOwnership = _out320;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1591_dims = _source74.dtor_dims;
          DAST._IType _1592_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            BigInteger _1593_i;
            _1593_i = (new BigInteger((_1591_dims).Count)) - (BigInteger.One);
            RAST._IType _1594_genTyp;
            RAST._IType _out321;
            _out321 = (this).GenType(_1592_typ, false, false);
            _1594_genTyp = _out321;
            Dafny.ISequence<Dafny.Rune> _1595_s;
            _1595_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1594_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1593_i).Sign != -1) {
              RAST._IExpr _1596_recursiveGen;
              DCOMP._IOwnership _1597___v106;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1598_recIdents;
              RAST._IExpr _out322;
              DCOMP._IOwnership _out323;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
              (this).GenExpr((_1591_dims).Select(_1593_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
              _1596_recursiveGen = _out322;
              _1597___v106 = _out323;
              _1598_recIdents = _out324;
              _1595_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1595_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1596_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1598_recIdents);
              _1593_i = (_1593_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1595_s);
            RAST._IExpr _out325;
            DCOMP._IOwnership _out326;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out325, out _out326);
            r = _out325;
            resultingOwnership = _out326;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DatatypeValue) {
          DAST._IDatatypeType _1599_datatypeType = _source74.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1600_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1601_variant = _source74.dtor_variant;
          bool _1602_isCo = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1603_values = _source74.dtor_contents;
          unmatched74 = false;
          {
            RAST._IExpr _out327;
            _out327 = DCOMP.COMP.GenPathExpr((_1599_datatypeType).dtor_path);
            r = _out327;
            Dafny.ISequence<RAST._IType> _1604_genTypeArgs;
            _1604_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi33 = new BigInteger((_1600_typeArgs).Count);
            for (BigInteger _1605_i = BigInteger.Zero; _1605_i < _hi33; _1605_i++) {
              RAST._IType _1606_typeExpr;
              RAST._IType _out328;
              _out328 = (this).GenType((_1600_typeArgs).Select(_1605_i), false, false);
              _1606_typeExpr = _out328;
              _1604_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1604_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1606_typeExpr));
            }
            if ((new BigInteger((_1600_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1604_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1601_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1607_assignments;
            _1607_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi34 = new BigInteger((_1603_values).Count);
            for (BigInteger _1608_i = BigInteger.Zero; _1608_i < _hi34; _1608_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_1603_values).Select(_1608_i);
              Dafny.ISequence<Dafny.Rune> _1609_name = _let_tmp_rhs63.dtor__0;
              DAST._IExpression _1610_value = _let_tmp_rhs63.dtor__1;
              if (_1602_isCo) {
                RAST._IExpr _1611_recursiveGen;
                DCOMP._IOwnership _1612___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1610_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1611_recursiveGen = _out329;
                _1612___v107 = _out330;
                _1613_recIdents = _out331;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1613_recIdents);
                Dafny.ISequence<Dafny.Rune> _1614_allReadCloned;
                _1614_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1613_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1615_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1613_recIdents).Elements) {
                    _1615_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1613_recIdents).Contains(_1615_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 3173)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1614_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1614_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1615_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1615_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1613_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1613_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1615_next));
                }
                Dafny.ISequence<Dafny.Rune> _1616_wasAssigned;
                _1616_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1614_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1611_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1607_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1607_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1609_name, RAST.Expr.create_RawExpr(_1616_wasAssigned))));
              } else {
                RAST._IExpr _1617_recursiveGen;
                DCOMP._IOwnership _1618___v108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_recIdents;
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExpr(_1610_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out332, out _out333, out _out334);
                _1617_recursiveGen = _out332;
                _1618___v108 = _out333;
                _1619_recIdents = _out334;
                _1607_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1607_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1609_name, _1617_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1619_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1607_assignments);
            r = RAST.__default.RcNew(r);
            RAST._IExpr _out335;
            DCOMP._IOwnership _out336;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out335, out _out336);
            r = _out335;
            resultingOwnership = _out336;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Convert) {
          DAST._IExpression _1620___v109 = _source74.dtor_value;
          DAST._IType _1621___v110 = _source74.dtor_from;
          DAST._IType _1622___v111 = _source74.dtor_typ;
          unmatched74 = false;
          {
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
            r = _out337;
            resultingOwnership = _out338;
            readIdents = _out339;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqConstruct) {
          DAST._IExpression _1623_length = _source74.dtor_length;
          DAST._IExpression _1624_expr = _source74.dtor_elem;
          unmatched74 = false;
          {
            RAST._IExpr _1625_recursiveGen;
            DCOMP._IOwnership _1626___v112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627_recIdents;
            RAST._IExpr _out340;
            DCOMP._IOwnership _out341;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
            (this).GenExpr(_1624_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out340, out _out341, out _out342);
            _1625_recursiveGen = _out340;
            _1626___v112 = _out341;
            _1627_recIdents = _out342;
            RAST._IExpr _1628_lengthGen;
            DCOMP._IOwnership _1629___v113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1630_lengthIdents;
            RAST._IExpr _out343;
            DCOMP._IOwnership _out344;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
            (this).GenExpr(_1623_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out343, out _out344, out _out345);
            _1628_lengthGen = _out343;
            _1629___v113 = _out344;
            _1630_lengthIdents = _out345;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1625_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1628_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1627_recIdents, _1630_lengthIdents);
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out346, out _out347);
            r = _out346;
            resultingOwnership = _out347;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1631_exprs = _source74.dtor_elements;
          DAST._IType _1632_typ = _source74.dtor_typ;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1633_genTpe;
            RAST._IType _out348;
            _out348 = (this).GenType(_1632_typ, false, false);
            _1633_genTpe = _out348;
            BigInteger _1634_i;
            _1634_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1635_args;
            _1635_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1634_i) < (new BigInteger((_1631_exprs).Count))) {
              RAST._IExpr _1636_recursiveGen;
              DCOMP._IOwnership _1637___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1638_recIdents;
              RAST._IExpr _out349;
              DCOMP._IOwnership _out350;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
              (this).GenExpr((_1631_exprs).Select(_1634_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out349, out _out350, out _out351);
              _1636_recursiveGen = _out349;
              _1637___v114 = _out350;
              _1638_recIdents = _out351;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1638_recIdents);
              _1635_args = Dafny.Sequence<RAST._IExpr>.Concat(_1635_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1636_recursiveGen));
              _1634_i = (_1634_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1635_args);
            if ((new BigInteger((_1635_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1633_genTpe));
            }
            RAST._IExpr _out352;
            DCOMP._IOwnership _out353;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out352, out _out353);
            r = _out352;
            resultingOwnership = _out353;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1639_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1640_generatedValues;
            _1640_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1641_i;
            _1641_i = BigInteger.Zero;
            while ((_1641_i) < (new BigInteger((_1639_exprs).Count))) {
              RAST._IExpr _1642_recursiveGen;
              DCOMP._IOwnership _1643___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
              RAST._IExpr _out354;
              DCOMP._IOwnership _out355;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
              (this).GenExpr((_1639_exprs).Select(_1641_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out354, out _out355, out _out356);
              _1642_recursiveGen = _out354;
              _1643___v115 = _out355;
              _1644_recIdents = _out356;
              _1640_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1640_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1642_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1644_recIdents);
              _1641_i = (_1641_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1640_generatedValues);
            RAST._IExpr _out357;
            DCOMP._IOwnership _out358;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out357, out _out358);
            r = _out357;
            resultingOwnership = _out358;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1645_exprs = _source74.dtor_elements;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1646_generatedValues;
            _1646_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1647_i;
            _1647_i = BigInteger.Zero;
            while ((_1647_i) < (new BigInteger((_1645_exprs).Count))) {
              RAST._IExpr _1648_recursiveGen;
              DCOMP._IOwnership _1649___v116;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdents;
              RAST._IExpr _out359;
              DCOMP._IOwnership _out360;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
              (this).GenExpr((_1645_exprs).Select(_1647_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out359, out _out360, out _out361);
              _1648_recursiveGen = _out359;
              _1649___v116 = _out360;
              _1650_recIdents = _out361;
              _1646_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1646_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1648_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1650_recIdents);
              _1647_i = (_1647_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1646_generatedValues);
            RAST._IExpr _out362;
            DCOMP._IOwnership _out363;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out362, out _out363);
            r = _out362;
            resultingOwnership = _out363;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_ToMultiset) {
          DAST._IExpression _1651_expr = _source74.dtor_ToMultiset_a0;
          unmatched74 = false;
          {
            RAST._IExpr _1652_recursiveGen;
            DCOMP._IOwnership _1653___v117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654_recIdents;
            RAST._IExpr _out364;
            DCOMP._IOwnership _out365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
            (this).GenExpr(_1651_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out364, out _out365, out _out366);
            _1652_recursiveGen = _out364;
            _1653___v117 = _out365;
            _1654_recIdents = _out366;
            r = ((_1652_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1654_recIdents;
            RAST._IExpr _out367;
            DCOMP._IOwnership _out368;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out367, out _out368);
            r = _out367;
            resultingOwnership = _out368;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1655_mapElems = _source74.dtor_mapElems;
          unmatched74 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1656_generatedValues;
            _1656_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1657_i;
            _1657_i = BigInteger.Zero;
            while ((_1657_i) < (new BigInteger((_1655_mapElems).Count))) {
              RAST._IExpr _1658_recursiveGenKey;
              DCOMP._IOwnership _1659___v118;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdentsKey;
              RAST._IExpr _out369;
              DCOMP._IOwnership _out370;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
              (this).GenExpr(((_1655_mapElems).Select(_1657_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
              _1658_recursiveGenKey = _out369;
              _1659___v118 = _out370;
              _1660_recIdentsKey = _out371;
              RAST._IExpr _1661_recursiveGenValue;
              DCOMP._IOwnership _1662___v119;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1663_recIdentsValue;
              RAST._IExpr _out372;
              DCOMP._IOwnership _out373;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out374;
              (this).GenExpr(((_1655_mapElems).Select(_1657_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out372, out _out373, out _out374);
              _1661_recursiveGenValue = _out372;
              _1662___v119 = _out373;
              _1663_recIdentsValue = _out374;
              _1656_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1656_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1658_recursiveGenKey, _1661_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1660_recIdentsKey), _1663_recIdentsValue);
              _1657_i = (_1657_i) + (BigInteger.One);
            }
            _1657_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1664_arguments;
            _1664_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1657_i) < (new BigInteger((_1656_generatedValues).Count))) {
              RAST._IExpr _1665_genKey;
              _1665_genKey = ((_1656_generatedValues).Select(_1657_i)).dtor__0;
              RAST._IExpr _1666_genValue;
              _1666_genValue = ((_1656_generatedValues).Select(_1657_i)).dtor__1;
              _1664_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1664_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1665_genKey, _1666_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1657_i = (_1657_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1664_arguments);
            RAST._IExpr _out375;
            DCOMP._IOwnership _out376;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out375, out _out376);
            r = _out375;
            resultingOwnership = _out376;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqUpdate) {
          DAST._IExpression _1667_expr = _source74.dtor_expr;
          DAST._IExpression _1668_index = _source74.dtor_indexExpr;
          DAST._IExpression _1669_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1670_exprR;
            DCOMP._IOwnership _1671___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_exprIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
            (this).GenExpr(_1667_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out377, out _out378, out _out379);
            _1670_exprR = _out377;
            _1671___v120 = _out378;
            _1672_exprIdents = _out379;
            RAST._IExpr _1673_indexR;
            DCOMP._IOwnership _1674_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_indexIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1668_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out380, out _out381, out _out382);
            _1673_indexR = _out380;
            _1674_indexOwnership = _out381;
            _1675_indexIdents = _out382;
            RAST._IExpr _1676_valueR;
            DCOMP._IOwnership _1677_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_valueIdents;
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
            (this).GenExpr(_1669_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out383, out _out384, out _out385);
            _1676_valueR = _out383;
            _1677_valueOwnership = _out384;
            _1678_valueIdents = _out385;
            r = ((_1670_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1673_indexR, _1676_valueR));
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out386, out _out387);
            r = _out386;
            resultingOwnership = _out387;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1672_exprIdents, _1675_indexIdents), _1678_valueIdents);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapUpdate) {
          DAST._IExpression _1679_expr = _source74.dtor_expr;
          DAST._IExpression _1680_index = _source74.dtor_indexExpr;
          DAST._IExpression _1681_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1682_exprR;
            DCOMP._IOwnership _1683___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_exprIdents;
            RAST._IExpr _out388;
            DCOMP._IOwnership _out389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
            (this).GenExpr(_1679_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out388, out _out389, out _out390);
            _1682_exprR = _out388;
            _1683___v121 = _out389;
            _1684_exprIdents = _out390;
            RAST._IExpr _1685_indexR;
            DCOMP._IOwnership _1686_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_indexIdents;
            RAST._IExpr _out391;
            DCOMP._IOwnership _out392;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
            (this).GenExpr(_1680_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out391, out _out392, out _out393);
            _1685_indexR = _out391;
            _1686_indexOwnership = _out392;
            _1687_indexIdents = _out393;
            RAST._IExpr _1688_valueR;
            DCOMP._IOwnership _1689_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_valueIdents;
            RAST._IExpr _out394;
            DCOMP._IOwnership _out395;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
            (this).GenExpr(_1681_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out394, out _out395, out _out396);
            _1688_valueR = _out394;
            _1689_valueOwnership = _out395;
            _1690_valueIdents = _out396;
            r = ((_1682_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1685_indexR, _1688_valueR));
            RAST._IExpr _out397;
            DCOMP._IOwnership _out398;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out397, out _out398);
            r = _out397;
            resultingOwnership = _out398;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1684_exprIdents, _1687_indexIdents), _1690_valueIdents);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_This) {
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = selfIdent;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1691_id = _source75.dtor_value;
                unmatched75 = false;
                {
                  r = RAST.Expr.create_Identifier(_1691_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                    r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1691_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1691_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1691_id);
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out399;
                DCOMP._IOwnership _out400;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out399, out _out400);
                r = _out399;
                resultingOwnership = _out400;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Ite) {
          DAST._IExpression _1692_cond = _source74.dtor_cond;
          DAST._IExpression _1693_t = _source74.dtor_thn;
          DAST._IExpression _1694_f = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1695_cond;
            DCOMP._IOwnership _1696___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1697_recIdentsCond;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1692_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1695_cond = _out401;
            _1696___v122 = _out402;
            _1697_recIdentsCond = _out403;
            Dafny.ISequence<Dafny.Rune> _1698_condString;
            _1698_condString = (_1695_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1699___v123;
            DCOMP._IOwnership _1700_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701___v124;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1693_t, selfIdent, env, expectedOwnership, out _out404, out _out405, out _out406);
            _1699___v123 = _out404;
            _1700_tHasToBeOwned = _out405;
            _1701___v124 = _out406;
            RAST._IExpr _1702_fExpr;
            DCOMP._IOwnership _1703_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1704_recIdentsF;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1694_f, selfIdent, env, _1700_tHasToBeOwned, out _out407, out _out408, out _out409);
            _1702_fExpr = _out407;
            _1703_fOwned = _out408;
            _1704_recIdentsF = _out409;
            Dafny.ISequence<Dafny.Rune> _1705_fString;
            _1705_fString = (_1702_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1706_tExpr;
            DCOMP._IOwnership _1707___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1708_recIdentsT;
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
            (this).GenExpr(_1693_t, selfIdent, env, _1703_fOwned, out _out410, out _out411, out _out412);
            _1706_tExpr = _out410;
            _1707___v125 = _out411;
            _1708_recIdentsT = _out412;
            Dafny.ISequence<Dafny.Rune> _1709_tString;
            _1709_tString = (_1706_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1698_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1709_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1705_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out413;
            DCOMP._IOwnership _out414;
            DCOMP.COMP.FromOwnership(r, _1703_fOwned, expectedOwnership, out _out413, out _out414);
            r = _out413;
            resultingOwnership = _out414;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1697_recIdentsCond, _1708_recIdentsT), _1704_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source74.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1710_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1711_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1712_recursiveGen;
              DCOMP._IOwnership _1713___v126;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdents;
              RAST._IExpr _out415;
              DCOMP._IOwnership _out416;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
              (this).GenExpr(_1710_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out415, out _out416, out _out417);
              _1712_recursiveGen = _out415;
              _1713___v126 = _out416;
              _1714_recIdents = _out417;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1712_recursiveGen, _1711_format);
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out418, out _out419);
              r = _out418;
              resultingOwnership = _out419;
              readIdents = _1714_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source74.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1715_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1716_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1717_recursiveGen;
              DCOMP._IOwnership _1718___v127;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdents;
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out422;
              (this).GenExpr(_1715_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out420, out _out421, out _out422);
              _1717_recursiveGen = _out420;
              _1718___v127 = _out421;
              _1719_recIdents = _out422;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1717_recursiveGen, _1716_format);
              RAST._IExpr _out423;
              DCOMP._IOwnership _out424;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out423, out _out424);
              r = _out423;
              resultingOwnership = _out424;
              readIdents = _1719_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source74.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1720_e = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _1721_format = _source74.dtor_format1;
            unmatched74 = false;
            {
              RAST._IExpr _1722_recursiveGen;
              DCOMP._IOwnership _1723_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
              RAST._IExpr _out425;
              DCOMP._IOwnership _out426;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
              (this).GenExpr(_1720_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out425, out _out426, out _out427);
              _1722_recursiveGen = _out425;
              _1723_recOwned = _out426;
              _1724_recIdents = _out427;
              r = ((_1722_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out428;
              DCOMP._IOwnership _out429;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out428, out _out429);
              r = _out428;
              resultingOwnership = _out429;
              readIdents = _1724_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BinOp) {
          DAST._IBinOp _1725___v128 = _source74.dtor_op;
          DAST._IExpression _1726___v129 = _source74.dtor_left;
          DAST._IExpression _1727___v130 = _source74.dtor_right;
          DAST.Format._IBinaryOpFormat _1728___v131 = _source74.dtor_format2;
          unmatched74 = false;
          RAST._IExpr _out430;
          DCOMP._IOwnership _out431;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out430, out _out431, out _out432);
          r = _out430;
          resultingOwnership = _out431;
          readIdents = _out432;
        }
      }
      if (unmatched74) {
        if (_source74.is_ArrayLen) {
          DAST._IExpression _1729_expr = _source74.dtor_expr;
          BigInteger _1730_dim = _source74.dtor_dim;
          unmatched74 = false;
          {
            RAST._IExpr _1731_recursiveGen;
            DCOMP._IOwnership _1732___v132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_recIdents;
            RAST._IExpr _out433;
            DCOMP._IOwnership _out434;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
            (this).GenExpr(_1729_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out433, out _out434, out _out435);
            _1731_recursiveGen = _out433;
            _1732___v132 = _out434;
            _1733_recIdents = _out435;
            if ((_1730_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1731_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1734_s;
              _1734_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1735_i;
              _1735_i = BigInteger.One;
              while ((_1735_i) < (_1730_dim)) {
                _1734_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1734_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1735_i = (_1735_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1731_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1734_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out436;
            DCOMP._IOwnership _out437;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out436, out _out437);
            r = _out436;
            resultingOwnership = _out437;
            readIdents = _1733_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapKeys) {
          DAST._IExpression _1736_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1737_recursiveGen;
            DCOMP._IOwnership _1738___v133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1739_recIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1736_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out438, out _out439, out _out440);
            _1737_recursiveGen = _out438;
            _1738___v133 = _out439;
            _1739_recIdents = _out440;
            readIdents = _1739_recIdents;
            r = ((_1737_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out441, out _out442);
            r = _out441;
            resultingOwnership = _out442;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapValues) {
          DAST._IExpression _1740_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1741_recursiveGen;
            DCOMP._IOwnership _1742___v134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1743_recIdents;
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
            (this).GenExpr(_1740_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out443, out _out444, out _out445);
            _1741_recursiveGen = _out443;
            _1742___v134 = _out444;
            _1743_recIdents = _out445;
            readIdents = _1743_recIdents;
            r = ((_1741_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out446, out _out447);
            r = _out446;
            resultingOwnership = _out447;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SelectFn) {
          DAST._IExpression _1744_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1745_field = _source74.dtor_field;
          bool _1746_isDatatype = _source74.dtor_onDatatype;
          bool _1747_isStatic = _source74.dtor_isStatic;
          BigInteger _1748_arity = _source74.dtor_arity;
          unmatched74 = false;
          {
            RAST._IExpr _1749_onExpr;
            DCOMP._IOwnership _1750_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_1744_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _1749_onExpr = _out448;
            _1750_onOwned = _out449;
            _1751_recIdents = _out450;
            Dafny.ISequence<Dafny.Rune> _1752_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1753_onString;
            _1753_onString = (_1749_onExpr)._ToString(DCOMP.__default.IND);
            if (_1747_isStatic) {
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1753_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1745_field));
            } else {
              _1752_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1752_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1753_onString), ((object.Equals(_1750_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1754_args;
              _1754_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1755_i;
              _1755_i = BigInteger.Zero;
              while ((_1755_i) < (_1748_arity)) {
                if ((_1755_i).Sign == 1) {
                  _1754_args = Dafny.Sequence<Dafny.Rune>.Concat(_1754_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1754_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1754_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1755_i));
                _1755_i = (_1755_i) + (BigInteger.One);
              }
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1752_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1754_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1752_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1745_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1754_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(_1752_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(_1752_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1756_typeShape;
            _1756_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1757_i;
            _1757_i = BigInteger.Zero;
            while ((_1757_i) < (_1748_arity)) {
              if ((_1757_i).Sign == 1) {
                _1756_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1756_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1756_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1756_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1757_i = (_1757_i) + (BigInteger.One);
            }
            _1756_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1756_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1752_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1752_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1756_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1752_s);
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = _1751_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression expr0 = _source74.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1758_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<Dafny.Rune> _1759_field = _source74.dtor_field;
            bool _1760_isConstant = _source74.dtor_isConstant;
            bool _1761_isDatatype = _source74.dtor_onDatatype;
            DAST._IType _1762_fieldType = _source74.dtor_fieldType;
            unmatched74 = false;
            {
              RAST._IExpr _1763_onExpr;
              DCOMP._IOwnership _1764_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
              RAST._IExpr _out453;
              DCOMP._IOwnership _out454;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
              (this).GenExpr(DAST.Expression.create_Companion(_1758_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out453, out _out454, out _out455);
              _1763_onExpr = _out453;
              _1764_onOwned = _out454;
              _1765_recIdents = _out455;
              r = ((_1763_onExpr).MSel(DCOMP.__default.escapeName(_1759_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out456;
              DCOMP._IOwnership _out457;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out456, out _out457);
              r = _out456;
              resultingOwnership = _out457;
              readIdents = _1765_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression _1766_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1767_field = _source74.dtor_field;
          bool _1768_isConstant = _source74.dtor_isConstant;
          bool _1769_isDatatype = _source74.dtor_onDatatype;
          DAST._IType _1770_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            if (_1769_isDatatype) {
              RAST._IExpr _1771_onExpr;
              DCOMP._IOwnership _1772_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_recIdents;
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExpr(_1766_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out458, out _out459, out _out460);
              _1771_onExpr = _out458;
              _1772_onOwned = _out459;
              _1773_recIdents = _out460;
              r = ((_1771_onExpr).Sel(DCOMP.__default.escapeName(_1767_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1774_typ;
              RAST._IType _out461;
              _out461 = (this).GenType(_1770_fieldType, false, false);
              _1774_typ = _out461;
              if (((_1774_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out462;
                DCOMP._IOwnership _out463;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out462, out _out463);
                r = _out462;
                resultingOwnership = _out463;
              }
              readIdents = _1773_recIdents;
            } else {
              RAST._IExpr _1775_onExpr;
              DCOMP._IOwnership _1776_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1777_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(_1766_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out464, out _out465, out _out466);
              _1775_onExpr = _out464;
              _1776_onOwned = _out465;
              _1777_recIdents = _out466;
              r = _1775_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_1767_field));
              if (_1768_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _1778_s;
                _1778_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1775_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_1767_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_1778_s);
              }
              DCOMP._IOwnership _1779_fromOwnership;
              _1779_fromOwnership = ((_1768_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              DCOMP.COMP.FromOwnership(r, _1779_fromOwnership, expectedOwnership, out _out467, out _out468);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _1777_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Index) {
          DAST._IExpression _1780_on = _source74.dtor_expr;
          DAST._ICollKind _1781_collKind = _source74.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1782_indices = _source74.dtor_indices;
          unmatched74 = false;
          {
            RAST._IExpr _1783_onExpr;
            DCOMP._IOwnership _1784_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1785_recIdents;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_1780_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out469, out _out470, out _out471);
            _1783_onExpr = _out469;
            _1784_onOwned = _out470;
            _1785_recIdents = _out471;
            readIdents = _1785_recIdents;
            r = _1783_onExpr;
            BigInteger _1786_i;
            _1786_i = BigInteger.Zero;
            while ((_1786_i) < (new BigInteger((_1782_indices).Count))) {
              if (object.Equals(_1781_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1787_idx;
              DCOMP._IOwnership _1788_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdentsIdx;
              RAST._IExpr _out472;
              DCOMP._IOwnership _out473;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
              (this).GenExpr((_1782_indices).Select(_1786_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out472, out _out473, out _out474);
              _1787_idx = _out472;
              _1788_idxOwned = _out473;
              _1789_recIdentsIdx = _out474;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1787_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1789_recIdentsIdx);
              _1786_i = (_1786_i) + (BigInteger.One);
            }
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IndexRange) {
          DAST._IExpression _1790_on = _source74.dtor_expr;
          bool _1791_isArray = _source74.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1792_low = _source74.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1793_high = _source74.dtor_high;
          unmatched74 = false;
          {
            RAST._IExpr _1794_onExpr;
            DCOMP._IOwnership _1795_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdents;
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
            (this).GenExpr(_1790_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out477, out _out478, out _out479);
            _1794_onExpr = _out477;
            _1795_onOwned = _out478;
            _1796_recIdents = _out479;
            readIdents = _1796_recIdents;
            Dafny.ISequence<Dafny.Rune> _1797_methodName;
            _1797_methodName = (((_1792_low).is_Some) ? ((((_1793_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1793_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1798_arguments;
            _1798_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source76 = _1792_low;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IExpression _1799_l = _source76.dtor_value;
                unmatched76 = false;
                {
                  RAST._IExpr _1800_lExpr;
                  DCOMP._IOwnership _1801___v135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1802_recIdentsL;
                  RAST._IExpr _out480;
                  DCOMP._IOwnership _out481;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
                  (this).GenExpr(_1799_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out480, out _out481, out _out482);
                  _1800_lExpr = _out480;
                  _1801___v135 = _out481;
                  _1802_recIdentsL = _out482;
                  _1798_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1798_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1800_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1802_recIdentsL);
                }
              }
            }
            if (unmatched76) {
              unmatched76 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source77 = _1793_high;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                DAST._IExpression _1803_h = _source77.dtor_value;
                unmatched77 = false;
                {
                  RAST._IExpr _1804_hExpr;
                  DCOMP._IOwnership _1805___v136;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1806_recIdentsH;
                  RAST._IExpr _out483;
                  DCOMP._IOwnership _out484;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
                  (this).GenExpr(_1803_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out483, out _out484, out _out485);
                  _1804_hExpr = _out483;
                  _1805___v136 = _out484;
                  _1806_recIdentsH = _out485;
                  _1798_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1798_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1804_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1806_recIdentsH);
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
            }
            r = _1794_onExpr;
            if (_1791_isArray) {
              if (!(_1797_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1797_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1797_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1797_methodName))).Apply(_1798_arguments);
            } else {
              if (!(_1797_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1797_methodName)).Apply(_1798_arguments);
              }
            }
            RAST._IExpr _out486;
            DCOMP._IOwnership _out487;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out486, out _out487);
            r = _out486;
            resultingOwnership = _out487;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TupleSelect) {
          DAST._IExpression _1807_on = _source74.dtor_expr;
          BigInteger _1808_idx = _source74.dtor_index;
          DAST._IType _1809_fieldType = _source74.dtor_fieldType;
          unmatched74 = false;
          {
            RAST._IExpr _1810_onExpr;
            DCOMP._IOwnership _1811_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1812_recIdents;
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
            (this).GenExpr(_1807_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out488, out _out489, out _out490);
            _1810_onExpr = _out488;
            _1811_onOwnership = _out489;
            _1812_recIdents = _out490;
            Dafny.ISequence<Dafny.Rune> _1813_selName;
            _1813_selName = Std.Strings.__default.OfNat(_1808_idx);
            DAST._IType _source78 = _1809_fieldType;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1814_tps = _source78.dtor_Tuple_a0;
                unmatched78 = false;
                if (((_1809_fieldType).is_Tuple) && ((new BigInteger((_1814_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _1813_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1813_selName);
                }
              }
            }
            if (unmatched78) {
              DAST._IType _1815___v137 = _source78;
              unmatched78 = false;
            }
            r = (_1810_onExpr).Sel(_1813_selName);
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            DCOMP.COMP.FromOwnership(r, _1811_onOwnership, expectedOwnership, out _out491, out _out492);
            r = _out491;
            resultingOwnership = _out492;
            readIdents = _1812_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Call) {
          DAST._IExpression _1816_on = _source74.dtor_on;
          DAST._ICallName _1817_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1818_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1819_args = _source74.dtor_args;
          unmatched74 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IExpr _1820_onExpr;
            DCOMP._IOwnership _1821___v138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1822_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1816_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out493, out _out494, out _out495);
            _1820_onExpr = _out493;
            _1821___v138 = _out494;
            _1822_recIdents = _out495;
            Dafny.ISequence<RAST._IType> _1823_typeExprs;
            _1823_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1818_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _hi35 = new BigInteger((_1818_typeArgs).Count);
              for (BigInteger _1824_typeI = BigInteger.Zero; _1824_typeI < _hi35; _1824_typeI++) {
                RAST._IType _1825_typeExpr;
                RAST._IType _out496;
                _out496 = (this).GenType((_1818_typeArgs).Select(_1824_typeI), false, false);
                _1825_typeExpr = _out496;
                _1823_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1823_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1825_typeExpr));
              }
            }
            Dafny.ISequence<RAST._IExpr> _1826_argExprs;
            _1826_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi36 = new BigInteger((_1819_args).Count);
            for (BigInteger _1827_i = BigInteger.Zero; _1827_i < _hi36; _1827_i++) {
              DCOMP._IOwnership _1828_argOwnership;
              _1828_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              if (((_1817_name).is_CallName) && ((_1827_i) < (new BigInteger((((_1817_name).dtor_signature)).Count)))) {
                RAST._IType _1829_tpe;
                RAST._IType _out497;
                _out497 = (this).GenType(((((_1817_name).dtor_signature)).Select(_1827_i)).dtor_typ, false, false);
                _1829_tpe = _out497;
                if ((_1829_tpe).CanReadWithoutClone()) {
                  _1828_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
                }
              }
              RAST._IExpr _1830_argExpr;
              DCOMP._IOwnership _1831___v139;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1832_argIdents;
              RAST._IExpr _out498;
              DCOMP._IOwnership _out499;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
              (this).GenExpr((_1819_args).Select(_1827_i), selfIdent, env, _1828_argOwnership, out _out498, out _out499, out _out500);
              _1830_argExpr = _out498;
              _1831___v139 = _out499;
              _1832_argIdents = _out500;
              _1826_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1826_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1830_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1832_argIdents);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1822_recIdents);
            Dafny.ISequence<Dafny.Rune> _1833_renderedName;
            _1833_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source79 = _1817_name;
              bool unmatched79 = true;
              if (unmatched79) {
                if (_source79.is_CallName) {
                  Dafny.ISequence<Dafny.Rune> _1834_ident = _source79.dtor_name;
                  Std.Wrappers._IOption<DAST._IType> _1835___v140 = _source79.dtor_onType;
                  Dafny.ISequence<DAST._IFormal> _1836___v141 = _source79.dtor_signature;
                  unmatched79 = false;
                  return DCOMP.__default.escapeName(_1834_ident);
                }
              }
              if (unmatched79) {
                bool disjunctiveMatch12 = false;
                if (_source79.is_MapBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (_source79.is_SetBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched79 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched79) {
                bool disjunctiveMatch13 = false;
                disjunctiveMatch13 = true;
                disjunctiveMatch13 = true;
                if (disjunctiveMatch13) {
                  unmatched79 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source80 = _1816_on;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1837___v142 = _source80.dtor_Companion_a0;
                unmatched80 = false;
                {
                  _1820_onExpr = (_1820_onExpr).MSel(_1833_renderedName);
                }
              }
            }
            if (unmatched80) {
              DAST._IExpression _1838___v143 = _source80;
              unmatched80 = false;
              {
                _1820_onExpr = (_1820_onExpr).Sel(_1833_renderedName);
              }
            }
            r = _1820_onExpr;
            if ((new BigInteger((_1823_typeExprs).Count)).Sign == 1) {
              r = (r).ApplyType(_1823_typeExprs);
            }
            r = (r).Apply(_1826_argExprs);
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1839_paramsDafny = _source74.dtor_params;
          DAST._IType _1840_retType = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1841_body = _source74.dtor_body;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IFormal> _1842_params;
            Dafny.ISequence<RAST._IFormal> _out503;
            _out503 = (this).GenParams(_1839_paramsDafny);
            _1842_params = _out503;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1843_paramNames;
            _1843_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1844_paramTypesMap;
            _1844_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi37 = new BigInteger((_1842_params).Count);
            for (BigInteger _1845_i = BigInteger.Zero; _1845_i < _hi37; _1845_i++) {
              Dafny.ISequence<Dafny.Rune> _1846_name;
              _1846_name = ((_1842_params).Select(_1845_i)).dtor_name;
              _1843_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1843_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1846_name));
              _1844_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1844_paramTypesMap, _1846_name, ((_1842_params).Select(_1845_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _1847_env;
            _1847_env = DCOMP.Environment.create(_1843_paramNames, _1844_paramTypesMap);
            RAST._IExpr _1848_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdents;
            DCOMP._IEnvironment _1850___v144;
            RAST._IExpr _out504;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
            DCOMP._IEnvironment _out506;
            (this).GenStmts(_1841_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1847_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out504, out _out505, out _out506);
            _1848_recursiveGen = _out504;
            _1849_recIdents = _out505;
            _1850___v144 = _out506;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _1849_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1849_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1851_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_1851_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _1852_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_1851_paramNames).Contains(_1852_name)) {
                  _coll6.Add(_1852_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_1843_paramNames));
            RAST._IExpr _1853_allReadCloned;
            _1853_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_1849_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1854_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1849_recIdents).Elements) {
                _1854_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1849_recIdents).Contains(_1854_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3639)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1854_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1853_allReadCloned = (_1853_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                }
              } else if (!((_1843_paramNames).Contains(_1854_next))) {
                _1853_allReadCloned = (_1853_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1854_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_1854_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1854_next));
              }
              _1849_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1849_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1854_next));
            }
            RAST._IType _1855_retTypeGen;
            RAST._IType _out507;
            _out507 = (this).GenType(_1840_retType, false, true);
            _1855_retTypeGen = _out507;
            r = RAST.Expr.create_Block((_1853_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_1842_params, Std.Wrappers.Option<RAST._IType>.create_Some(_1855_retTypeGen), RAST.Expr.create_Block(_1848_recursiveGen)))));
            RAST._IExpr _out508;
            DCOMP._IOwnership _out509;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out508, out _out509);
            r = _out508;
            resultingOwnership = _out509;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1856_values = _source74.dtor_values;
          DAST._IType _1857_retType = _source74.dtor_retType;
          DAST._IExpression _1858_expr = _source74.dtor_expr;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1859_paramNames;
            _1859_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _1860_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out510;
            _out510 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_1861_value) => {
              return (_1861_value).dtor__0;
            })), _1856_values));
            _1860_paramFormals = _out510;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1862_paramTypes;
            _1862_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1863_paramNamesSet;
            _1863_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi38 = new BigInteger((_1856_values).Count);
            for (BigInteger _1864_i = BigInteger.Zero; _1864_i < _hi38; _1864_i++) {
              Dafny.ISequence<Dafny.Rune> _1865_name;
              _1865_name = (((_1856_values).Select(_1864_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _1866_rName;
              _1866_rName = DCOMP.__default.escapeName(_1865_name);
              _1859_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1859_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1866_rName));
              _1862_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1862_paramTypes, _1866_rName, ((_1860_paramFormals).Select(_1864_i)).dtor_tpe);
              _1863_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1863_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1866_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi39 = new BigInteger((_1856_values).Count);
            for (BigInteger _1867_i = BigInteger.Zero; _1867_i < _hi39; _1867_i++) {
              RAST._IType _1868_typeGen;
              RAST._IType _out511;
              _out511 = (this).GenType((((_1856_values).Select(_1867_i)).dtor__0).dtor_typ, false, true);
              _1868_typeGen = _out511;
              RAST._IExpr _1869_valueGen;
              DCOMP._IOwnership _1870___v145;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1871_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(((_1856_values).Select(_1867_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out512, out _out513, out _out514);
              _1869_valueGen = _out512;
              _1870___v145 = _out513;
              _1871_recIdents = _out514;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_1856_values).Select(_1867_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1868_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1869_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1871_recIdents);
            }
            DCOMP._IEnvironment _1872_newEnv;
            _1872_newEnv = DCOMP.Environment.create(_1859_paramNames, _1862_paramTypes);
            RAST._IExpr _1873_recGen;
            DCOMP._IOwnership _1874_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1875_recIdents;
            RAST._IExpr _out515;
            DCOMP._IOwnership _out516;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
            (this).GenExpr(_1858_expr, selfIdent, _1872_newEnv, expectedOwnership, out _out515, out _out516, out _out517);
            _1873_recGen = _out515;
            _1874_recOwned = _out516;
            _1875_recIdents = _out517;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1875_recIdents, _1863_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_1873_recGen));
            RAST._IExpr _out518;
            DCOMP._IOwnership _out519;
            DCOMP.COMP.FromOwnership(r, _1874_recOwned, expectedOwnership, out _out518, out _out519);
            r = _out518;
            resultingOwnership = _out519;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1876_name = _source74.dtor_name;
          DAST._IType _1877_tpe = _source74.dtor_typ;
          DAST._IExpression _1878_value = _source74.dtor_value;
          DAST._IExpression _1879_iifeBody = _source74.dtor_iifeBody;
          unmatched74 = false;
          {
            RAST._IExpr _1880_valueGen;
            DCOMP._IOwnership _1881___v146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1882_recIdents;
            RAST._IExpr _out520;
            DCOMP._IOwnership _out521;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
            (this).GenExpr(_1878_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out520, out _out521, out _out522);
            _1880_valueGen = _out520;
            _1881___v146 = _out521;
            _1882_recIdents = _out522;
            readIdents = _1882_recIdents;
            RAST._IType _1883_valueTypeGen;
            RAST._IType _out523;
            _out523 = (this).GenType(_1877_tpe, false, true);
            _1883_valueTypeGen = _out523;
            RAST._IExpr _1884_bodyGen;
            DCOMP._IOwnership _1885___v147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1886_bodyIdents;
            RAST._IExpr _out524;
            DCOMP._IOwnership _out525;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
            (this).GenExpr(_1879_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out524, out _out525, out _out526);
            _1884_bodyGen = _out524;
            _1885___v147 = _out525;
            _1886_bodyIdents = _out526;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1886_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_1876_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_1876_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_1883_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1880_valueGen))).Then(_1884_bodyGen));
            RAST._IExpr _out527;
            DCOMP._IOwnership _out528;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out527, out _out528);
            r = _out527;
            resultingOwnership = _out528;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Apply) {
          DAST._IExpression _1887_func = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1888_args = _source74.dtor_args;
          unmatched74 = false;
          {
            RAST._IExpr _1889_funcExpr;
            DCOMP._IOwnership _1890___v148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1891_recIdents;
            RAST._IExpr _out529;
            DCOMP._IOwnership _out530;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out531;
            (this).GenExpr(_1887_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out529, out _out530, out _out531);
            _1889_funcExpr = _out529;
            _1890___v148 = _out530;
            _1891_recIdents = _out531;
            readIdents = _1891_recIdents;
            Dafny.ISequence<RAST._IExpr> _1892_rArgs;
            _1892_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi40 = new BigInteger((_1888_args).Count);
            for (BigInteger _1893_i = BigInteger.Zero; _1893_i < _hi40; _1893_i++) {
              RAST._IExpr _1894_argExpr;
              DCOMP._IOwnership _1895_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1896_argIdents;
              RAST._IExpr _out532;
              DCOMP._IOwnership _out533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
              (this).GenExpr((_1888_args).Select(_1893_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out532, out _out533, out _out534);
              _1894_argExpr = _out532;
              _1895_argOwned = _out533;
              _1896_argIdents = _out534;
              _1892_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1892_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1894_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1896_argIdents);
            }
            r = (_1889_funcExpr).Apply(_1892_rArgs);
            RAST._IExpr _out535;
            DCOMP._IOwnership _out536;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out535, out _out536);
            r = _out535;
            resultingOwnership = _out536;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TypeTest) {
          DAST._IExpression _1897_on = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1898_dType = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1899_variant = _source74.dtor_variant;
          unmatched74 = false;
          {
            RAST._IExpr _1900_exprGen;
            DCOMP._IOwnership _1901___v149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
            RAST._IExpr _out537;
            DCOMP._IOwnership _out538;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out539;
            (this).GenExpr(_1897_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out537, out _out538, out _out539);
            _1900_exprGen = _out537;
            _1901___v149 = _out538;
            _1902_recIdents = _out539;
            RAST._IType _1903_dTypePath;
            RAST._IType _out540;
            _out540 = DCOMP.COMP.GenPath(_1898_dType);
            _1903_dTypePath = _out540;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_1900_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_1903_dTypePath).MSel(DCOMP.__default.escapeName(_1899_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out541, out _out542);
            r = _out541;
            resultingOwnership = _out542;
            readIdents = _1902_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_BoolBoundedPool) {
          unmatched74 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out543;
            DCOMP._IOwnership _out544;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out543, out _out544);
            r = _out543;
            resultingOwnership = _out544;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetBoundedPool) {
          DAST._IExpression _1904_of = _source74.dtor_of;
          unmatched74 = false;
          {
            RAST._IExpr _1905_exprGen;
            DCOMP._IOwnership _1906___v150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1907_recIdents;
            RAST._IExpr _out545;
            DCOMP._IOwnership _out546;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
            (this).GenExpr(_1904_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
            _1905_exprGen = _out545;
            _1906___v150 = _out546;
            _1907_recIdents = _out547;
            r = ((((_1905_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out548;
            DCOMP._IOwnership _out549;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out548, out _out549);
            r = _out548;
            resultingOwnership = _out549;
            readIdents = _1907_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SeqBoundedPool) {
          DAST._IExpression _1908_of = _source74.dtor_of;
          bool _1909_includeDuplicates = _source74.dtor_includeDuplicates;
          unmatched74 = false;
          {
            RAST._IExpr _1910_exprGen;
            DCOMP._IOwnership _1911___v151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
            (this).GenExpr(_1908_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
            _1910_exprGen = _out550;
            _1911___v151 = _out551;
            _1912_recIdents = _out552;
            r = ((_1910_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_1909_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            readIdents = _1912_recIdents;
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_IntRange) {
          DAST._IExpression _1913_lo = _source74.dtor_lo;
          DAST._IExpression _1914_hi = _source74.dtor_hi;
          unmatched74 = false;
          {
            RAST._IExpr _1915_lo;
            DCOMP._IOwnership _1916___v152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdentsLo;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_1913_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out555, out _out556, out _out557);
            _1915_lo = _out555;
            _1916___v152 = _out556;
            _1917_recIdentsLo = _out557;
            RAST._IExpr _1918_hi;
            DCOMP._IOwnership _1919___v153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1920_recIdentsHi;
            RAST._IExpr _out558;
            DCOMP._IOwnership _out559;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
            (this).GenExpr(_1914_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
            _1918_hi = _out558;
            _1919___v153 = _out559;
            _1920_recIdentsHi = _out560;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1915_lo, _1918_hi));
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out561, out _out562);
            r = _out561;
            resultingOwnership = _out562;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1917_recIdentsLo, _1920_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapBuilder) {
          DAST._IType _1921_keyType = _source74.dtor_keyType;
          DAST._IType _1922_valueType = _source74.dtor_valueType;
          unmatched74 = false;
          {
            RAST._IType _1923_kType;
            RAST._IType _out563;
            _out563 = (this).GenType(_1921_keyType, false, false);
            _1923_kType = _out563;
            RAST._IType _1924_vType;
            RAST._IType _out564;
            _out564 = (this).GenType(_1922_valueType, false, false);
            _1924_vType = _out564;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1923_kType, _1924_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out565, out _out566);
            r = _out565;
            resultingOwnership = _out566;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched74) {
        DAST._IType _1925_elemType = _source74.dtor_elemType;
        unmatched74 = false;
        {
          RAST._IType _1926_eType;
          RAST._IType _out567;
          _out567 = (this).GenType(_1925_elemType, false, false);
          _1926_eType = _out567;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1926_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out568;
          DCOMP._IOwnership _out569;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out568, out _out569);
          r = _out568;
          resultingOwnership = _out569;
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _1927_i;
      _1927_i = BigInteger.Zero;
      while ((_1927_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1928_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1929_m;
        RAST._IMod _out570;
        _out570 = (this).GenModule((p).Select(_1927_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1929_m = _out570;
        _1928_generated = (_1929_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1927_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1928_generated);
        _1927_i = (_1927_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1930_i;
      _1930_i = BigInteger.Zero;
      while ((_1930_i) < (new BigInteger((fullName).Count))) {
        if ((_1930_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_1930_i)));
        _1930_i = (_1930_i) + (BigInteger.One);
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
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP