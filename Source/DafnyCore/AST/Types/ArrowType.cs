using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ArrowType : UserDefinedType {

  public static Expression FrameArrowToObjectSet(Expression e, FreshIdGenerator idGen, BuiltIns builtIns) {
    Contract.Requires(e != null);
    Contract.Requires(idGen != null);
    Contract.Requires(builtIns != null);
    var arrTy = e.Type.AsArrowType;
    if (arrTy != null) {
      var bvars = new List<BoundVar>();
      var bexprs = new List<Expression>();
      foreach (var t in arrTy.Args) {
        var bv = new BoundVar(e.tok, idGen.FreshId("_x"), t);
        bvars.Add(bv);
        bexprs.Add(new IdentifierExpr(e.tok, bv.Name) { Type = bv.Type, Var = bv });
      }

      var oVar = new BoundVar(e.tok, idGen.FreshId("_o"), builtIns.ObjectQ());
      var obj = new IdentifierExpr(e.tok, oVar.Name) { Type = oVar.Type, Var = oVar };
      bvars.Add(oVar);
      var collection = new ApplyExpr(e.tok, e, bexprs, e.tok) {
        Type = new SetType(true, builtIns.ObjectQ())
      };
      ComputeResolvedOpcodeAndBoundedPool(collection, (CollectionType)arrTy.Result, out var resolvedOpcode, out _);

      return
        new SetComprehension(e.tok, e.RangeToken, true, bvars,
          new BinaryExpr(e.tok, BinaryExpr.Opcode.In, obj, collection) {
            ResolvedOp = resolvedOpcode,
            Type = Type.Bool
          }, obj, null) {
          Type = new SetType(true, builtIns.ObjectQ())
        };
    } else {
      return e;
    }
  }

  public static void ComputeResolvedOpcodeAndBoundedPool(Expression collection, CollectionType collectionType,
    out BinaryExpr.ResolvedOpcode resolvedOpcode, out ComprehensionExpr.BoundedPool boundedPool) {
    if (collectionType is SetType setType) {
      resolvedOpcode = BinaryExpr.ResolvedOpcode.InSet;
      boundedPool = new ComprehensionExpr.SetBoundedPool(collection, collectionType.Arg, collectionType.Arg, setType.Finite);
    } else if (collectionType is SeqType) {
      resolvedOpcode = BinaryExpr.ResolvedOpcode.InSeq;
      boundedPool = new ComprehensionExpr.SeqBoundedPool(collection, collectionType.Arg, collectionType.Arg);
    } else {
      Contract.Assert(collectionType is MultiSetType);
      resolvedOpcode = BinaryExpr.ResolvedOpcode.InMultiSet;
      boundedPool = new ComprehensionExpr.MultiSetBoundedPool(collection, collectionType.Arg, collectionType.Arg);
    }
  }

  public List<Type> Args {
    get { return TypeArgs.GetRange(0, Arity); }
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
  public ArrowType(IToken tok, List<Type> args, Type result)
    : base(tok, ArrowTypeName(args.Count), Util.Snoc(args, result)) {
    Contract.Requires(tok != null);
    Contract.Requires(args != null);
    Contract.Requires(result != null);
  }
  /// <summary>
  /// Constructs and returns a resolved arrow type.
  /// </summary>
  public ArrowType(IToken tok, ArrowTypeDecl atd, List<Type> typeArgsAndResult)
    : base(tok, ArrowTypeName(atd.Arity), atd, typeArgsAndResult) {
    Contract.Requires(tok != null);
    Contract.Requires(atd != null);
    Contract.Requires(typeArgsAndResult != null);
    Contract.Requires(typeArgsAndResult.Count == atd.Arity + 1);
  }
  /// <summary>
  /// Constructs and returns a resolved arrow type.
  /// </summary>
  public ArrowType(IToken tok, ArrowTypeDecl atd, List<Type> typeArgs, Type result)
    : this(tok, atd, Util.Snoc(typeArgs, result)) {
    Contract.Requires(tok != null);
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

  public override string TypeName(ModuleDefinition context, bool parseAble) {
    return PrettyArrowTypeName(ANY_ARROW, Args, Result, context, parseAble);
  }

  /// <summary>
  /// Pretty prints an arrow type.  If "result" is null, then all arguments, including the result type are expected in "typeArgs".
  /// If "result" is non-null, then only the in-arguments are in "typeArgs".
  /// </summary>
  public static string PrettyArrowTypeName(string arrow, List<Type> typeArgs, Type result, ModuleDefinition context, bool parseAble) {
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
      if (udt != null && ((udt.FullName != null && BuiltIns.IsTupleTypeName(udt.FullName)) || udt.ResolvedClass is TupleTypeDecl)) {
        domainNeedsParens = true;
      }
    }
    string s = "";
    if (domainNeedsParens) { s += "("; }
    s += Util.Comma(typeArgs.Take(arity), arg => arg.TypeName(context, parseAble));
    if (domainNeedsParens) { s += ")"; }
    s += " " + arrow + " ";
    if (result != null || typeArgs.Count >= 1) {
      s += (result ?? typeArgs.Last()).TypeName(context, parseAble);
    } else {
      s += "<unable to infer result type>";
    }
    return s;
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    return new ArrowType(tok, (ArrowTypeDecl)ResolvedClass, Args.ConvertAll(u => u.Subst(subst)), Result.Subst(subst));
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new ArrowType(tok, (ArrowTypeDecl)ResolvedClass, arguments);
  }

  public override bool SupportsEquality {
    get {
      return false;
    }
  }

  public override IEnumerable<Node> Children => Args.Concat(new List<Node>() { Result });
  public override IEnumerable<Node> PreResolveChildren => Args.Concat(new List<Node>() { Result });
}