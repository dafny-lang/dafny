using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ArrowType : UserDefinedType {

  public List<Type> Args {
    get { return TypeArgs.GetRange(0, Arity); }
  }

  public List<TypeParameter.TPVariance> Variances(bool negate = false) {
    if (negate) {
      return Enumerable.Range(0, Arity + 1).Select(i => i == Arity ? TypeParameter.TPVariance.Contra : TypeParameter.TPVariance.Co).ToList();
    } else {
      return Enumerable.Range(0, Arity + 1).Select(i => i == Arity ? TypeParameter.TPVariance.Co : TypeParameter.TPVariance.Contra).ToList();
    }
  }

  public Type Result {
    get { return TypeArgs[Arity]; }
  }

  public int Arity {
    get { return TypeArgs.Count - 1; }
  }

  /// <summary>
  /// Constructs a(n unresolved) arrow type.
  /// </summary>
  public ArrowType(IOrigin origin, List<Type> args, Type result)
    : base(origin, ArrowTypeName(args.Count), Util.Snoc(args, result)) {
    Contract.Requires(origin != null);
    Contract.Requires(args != null);
    Contract.Requires(result != null);
  }
  /// <summary>
  /// Constructs and returns a resolved arrow type.
  /// </summary>
  public ArrowType(IOrigin origin, ArrowTypeDecl atd, List<Type> typeArgsAndResult)
    : base(origin, ArrowTypeName(atd.Arity), atd, typeArgsAndResult) {
    Contract.Requires(origin != null);
    Contract.Requires(atd != null);
    Contract.Requires(typeArgsAndResult != null);
    Contract.Requires(typeArgsAndResult.Count == atd.Arity + 1);
  }
  /// <summary>
  /// Constructs and returns a resolved arrow type.
  /// </summary>
  public ArrowType(IOrigin origin, ArrowTypeDecl atd, List<Type> typeArgs, Type result)
    : this(origin, atd, Util.Snoc(typeArgs, result)) {
    Contract.Requires(origin != null);
    Contract.Requires(atd != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == atd.Arity);
    Contract.Requires(result != null);
  }

  public const string Arrow_FullCompileName = "Func";  // this is the same for all arities

  public static string ArrowTypeName(int arity) {
    return "_#Func" + arity;
  }

  [Pure]
  public static bool IsArrowTypeName(string s) {
    return s.StartsWith("_#Func");
  }

  public static string PartialArrowTypeName(int arity) {
    return "_#PartialFunc" + arity;
  }

  [Pure]
  public static bool IsPartialArrowTypeName(string s) {
    return s.StartsWith("_#PartialFunc");
  }

  public static string TotalArrowTypeName(int arity) {
    return "_#TotalFunc" + arity;
  }

  [Pure]
  public static bool IsTotalArrowTypeName(string s) {
    return s.StartsWith("_#TotalFunc");
  }

  public const string ANY_ARROW = "~>";
  public const string PARTIAL_ARROW = "-->";
  public const string TOTAL_ARROW = "->";

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return PrettyArrowTypeName(options, ANY_ARROW, Args, Result, context, parseAble);
  }

  /// <summary>
  /// Pretty prints an arrow type.  If "result" is null, then all arguments, including the result type are expected in "typeArgs".
  /// If "result" is non-null, then only the in-arguments are in "typeArgs".
  /// </summary>
  public static string PrettyArrowTypeName(DafnyOptions options, string arrow, List<Type> typeArgs, Type result, ModuleDefinition context, bool parseAble) {
    Contract.Requires(arrow != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(result != null || 1 <= typeArgs.Count);

    int arity = result == null ? typeArgs.Count - 1 : typeArgs.Count;
    var domainNeedsParens = false;
    if (arity != 1) {
      // 0 or 2-or-more arguments:  need parentheses
      domainNeedsParens = true;
    } else if (typeArgs[0].IsBuiltinArrowType) {
      // arrows are right associative, so we need parentheses around the domain type
      domainNeedsParens = true;
    } else {
      // if the domain type consists of a single tuple type, then an extra set of parentheses is needed
      // Note, we do NOT call .AsDatatype or .AsIndDatatype here, because those calls will do a NormalizeExpand().  Instead, we do the check manually.
      var udt = typeArgs[0].Normalize() as UserDefinedType;  // note, we do Normalize(), not NormalizeExpand(), since the TypeName will use any synonym
      if (udt != null && ((udt.FullName != null && SystemModuleManager.IsTupleTypeName(udt.FullName)) || udt.ResolvedClass is TupleTypeDecl)) {
        domainNeedsParens = true;
      }
    }
    string s = "";
    if (domainNeedsParens) { s += "("; }
    s += Util.Comma(typeArgs.Take(arity), arg => arg.TypeName(options, context, parseAble));
    if (domainNeedsParens) { s += ")"; }
    s += " " + arrow + " ";
    if (result != null || typeArgs.Count >= 1) {
      s += (result ?? typeArgs.Last()).TypeName(options, context, parseAble);
    } else {
      s += "<unable to infer result type>";
    }
    return s;
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    return new ArrowType(Origin, (ArrowTypeDecl)ResolvedClass, Args.ConvertAll(u => u.Subst(subst)), Result.Subst(subst));
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new ArrowType(Origin, (ArrowTypeDecl)ResolvedClass, arguments);
  }

  public override bool SupportsEquality {
    get {
      return false;
    }
  }

  public override IEnumerable<INode> Children => Args.Concat(new List<Node>() { Result });
  public override IEnumerable<INode> PreResolveChildren => Args.Concat(new List<Node>() { Result });
}