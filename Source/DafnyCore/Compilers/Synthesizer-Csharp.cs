using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis.CSharp;

namespace Microsoft.Dafny.Compilers;

/// <summary>
/// Below is the full grammar of ensures clauses that can specify
/// the behavior of an object returned by a synthesize-annotated method
/// (S is the starting symbol, ID refers to a variable/field/method/type
/// identifier, EXPR stands for an arbitrary Dafny expression):
///
/// S         = FORALL
///           | EQUALS 
///           | S && S
/// EQUALS    = ID.ID (ARGLIST)  == EXPR // stubs a method call
///           | ID.ID            == EXPR // stubs field access
///           | EQUALS && EQUALS
/// FORALL    = forall BOUNDVARS :: EXPR ==> EQUALS
/// ARGLIST   = ID   // this can be one of the bound variables
///           | EXPR // this expr may not reference any of the bound variables 
///           | ARGLIST, ARGLIST
/// BOUNDVARS = ID : ID 
///           | BOUNDVARS, BOUNDVARS
/// 
/// </summary>
public class CsharpSynthesizer {

  private readonly CsharpCompiler compiler;
  private readonly ConcreteSyntaxTree ErrorWriter;
  // maps identifiers to the names of the corresponding mock:
  private Dictionary<IVariable, string> objectToMockName = new();
  // associates a bound variable with the lambda passed to argument matcher
  private Dictionary<IVariable, string> bounds = new();
  private Method lastSynthesizedMethod = null;

  public CsharpSynthesizer(CsharpCompiler compiler, ConcreteSyntaxTree errorWriter) {
    this.compiler = compiler;
    ErrorWriter = errorWriter;
  }

  /// <summary>
  /// Create a body of a method that synthesizes one or more objects.
  /// For instance, the following Dafny method:
  /// 
  /// method {:synthesize} CrossReferentialMock()
  ///     returns (e1:Even, e2:Even) 
  ///     ensures fresh(e1) && fresh(e2) 
  ///     ensures e1.Next() == e2
  ///     ensures e2.Next() == e1
  ///
  /// Gets compiled to the following C# code:
  /// (Note that e1Return and e2Return are introduced because e1 and e2
  /// are used inside a lambda and cannot, therefore, be out parameters)
  ///
  /// public static void CrossReferentialMock(out Even e1Return,
  ///                                         out Even e2Return) {
  ///     var e1Mock = new Mock<Even>();
  ///     var e1 = e1Mock.Object;
  ///     var e2Mock = new Mock<Even>();
  ///     var e2 = e2Mock.Object;
  ///     e1Mock.Setup(x => x.Next()).Returns(()=>e2);
  ///     e2Mock.Setup(x => x.Next()).Returns(()=>e1);
  ///     e1Return = e1;
  ///     e2Return = e2;
  /// }
  /// </summary>
  public ConcreteSyntaxTree SynthesizeMethod(Method method,
    List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody,
    ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {

    lastSynthesizedMethod = method;
    // The following few lines are identical to those in Compiler.CreateMethod:
    var customReceiver = createBody &&
                         !forBodyInheritance &&
                         compiler.NeedsCustomReceiver(method);
    var keywords = compiler.Keywords(true, true);
    var returnType = compiler.GetTargetReturnTypeReplacement(method, wr);
    var typeParameters = compiler.TypeParameters(SinglePassCompiler.TypeArgumentInstantiation.
      ToFormals(compiler.ForTypeParameters(typeArgs, method, lookasideBody)));
    var parameters = compiler
      .GetMethodParameters(method, typeArgs, lookasideBody, customReceiver, returnType);

    // Out parameters cannot be used inside lambda expressions in Csharp
    // but the mocked objects may appear in lambda expressions during
    // mocking (e.g. two objects may cross-reference each other).
    // The solution is to rename the out parameters.
    var parameterString = parameters.ToString();
    var objectToReturnName = method.Outs.ToDictionary(o => o,
      o => compiler.idGenerator.FreshId(o.CompileName + "Return"));
    foreach (var (obj, returnName) in objectToReturnName) {
      parameterString = Regex.Replace(parameterString,
        $"(^|[^a-zA-Z0-9_]){obj.CompileName}([^a-zA-Z0-9_]|$)",
        "$1" + returnName + "$2");
    }
    wr.FormatLine($"{keywords}{returnType} {compiler.PublicIdProtect(method.CompileName)}{typeParameters}({parameterString}) {{");

    // Initialize the mocks
    objectToMockName = method.Outs.ToDictionary(o => (IVariable)o,
      o => compiler.idGenerator.FreshId(o.CompileName + "Mock"));
    foreach (var (obj, mockName) in objectToMockName) {
      var typeName = compiler.TypeName(obj.Type, wr, obj.Tok);
      wr.FormatLine($"var {mockName} = new Mock<{typeName}>();");
      wr.FormatLine($"{mockName}.CallBase = true;");
      wr.FormatLine($"var {obj.CompileName} = {mockName}.Object;");
    }

    // Stub methods and fields according to the Dafny post-conditions:
    foreach (var ensureClause in method.Ens) {
      bounds = new();
      var wStmts = wr.Fork();
      wr.Append(SynthesizeExpression(ensureClause.E, wStmts));
    }

    // Return the mocked objects:
    if (returnType != "void") {
      wr.FormatLine($"return {method.Outs[0].CompileName};");
    } else {
      foreach (var o in method.Outs) {
        wr.FormatLine($"{objectToReturnName[o]} = {o.CompileName};");
      }
    }
    wr.WriteLine("}");
    return wr;
  }

  /// <summary>
  /// If the expression is a bound variable identifier, return the
  /// variable and the string representation of the bounding condition
  /// </summary>
  private Tuple<IVariable, string> GetBound(Expression exp) {
    if (exp is not NameSegment) {
      return null;
    }
    var variable = ((IdentifierExpr)exp.Resolved).Var;
    if (!bounds.ContainsKey(variable)) {
      return null;
    }
    return new Tuple<IVariable, string>(variable, bounds[variable]);
  }

  private ConcreteSyntaxTree SynthesizeExpression(Expression expr, ConcreteSyntaxTree wStmts) {
    switch (expr) {
      case LiteralExpr literalExpr:
        return compiler.TrExpr(literalExpr, false, wStmts);
        break;
      case ApplySuffix applySuffix:
        return SynthesizeExpression(applySuffix, wStmts);
        break;
      case BinaryExpr binaryExpr:
        return SynthesizeExpression(binaryExpr, wStmts);
        break;
      case ForallExpr forallExpr:
        return SynthesizeExpression(forallExpr, wStmts);
        break;
      case FreshExpr:
        return new ConcreteSyntaxTree();
        break;
      default:
        // TODO: Have the resolver reject all these unimplemented cases,
        // or convert them to UnsupportedFeatureExceptions
        throw new NotImplementedException();
    }
  }

  private void SynthesizeExpression(ConcreteSyntaxTree wr, ApplySuffix applySuffix, ConcreteSyntaxTree wStmts) {

    var methodApp = (ExprDotName)applySuffix.Lhs;
    var receiver = ((IdentifierExpr)methodApp.Lhs.Resolved).Var;
    var method = ((MemberSelectExpr)methodApp.Resolved).Member;
    var methodName = method.CompileName;

    if (((Function)method).Ens.Count != 0) {
      compiler.Error(lastSynthesizedMethod.tok, "Post-conditions on function {0} might " +
                                 "be unsatisfied when synthesizing code " +
                                 "for method {1}", ErrorWriter,
        methodName, lastSynthesizedMethod.Name);
    }

    wr.Format($"{objectToMockName[receiver]}.Setup(x => x.{methodName}(");

    // The remaining part of the method uses Moq's argument matching to
    // describe the arguments for which the method should be stubbed
    // (in Dafny, this condition is the antecedent over bound variables)
    for (int i = 0; i < applySuffix.Args.Count; i++) {
      var arg = applySuffix.Args[i];
      var bound = GetBound(arg);
      if (bound != null) { // if true, arg is a bound variable
        wr.Write(bound.Item2);
      } else {
        wr.Append(compiler.TrExpr(arg, false, wStmts));
      }
      if (i != applySuffix.Args.Count - 1) {
        wr.Write(", ");
      }
    }
    wr.Write("))");
  }

  private void SynthesizeExpression(ConcreteSyntaxTree wr, BinaryExpr binaryExpr, ConcreteSyntaxTree wStmts) {
    if (binaryExpr.Op == BinaryExpr.Opcode.And) {
      Dictionary<IVariable, string> oldBounds = bounds
        .ToDictionary(entry => entry.Key, entry => entry.Value);
      wr.Append(SynthesizeExpression(binaryExpr.E0, wStmts));
      bounds = oldBounds;
      wr.Append(SynthesizeExpression(binaryExpr.E1, wStmts));
      return;
    }
    if (binaryExpr.Op != BinaryExpr.Opcode.Eq) {
      throw new NotImplementedException();
    }
    if (binaryExpr.E0 is ExprDotName exprDotName) { // field stubbing
      var obj = ((IdentifierExpr)exprDotName.Lhs.Resolved).Var;
      var field = ((MemberSelectExpr)exprDotName.Resolved).Member;
      var fieldName = field.CompileName;
      compiler.Error(lastSynthesizedMethod.tok, "Stubbing fields is not recommended " +
                                "(field {0} of object {1} inside method {2})",
        ErrorWriter, fieldName, obj.Name, lastSynthesizedMethod.Name);
      wr.Format($"{objectToMockName[obj]}.SetupGet({obj.CompileName} => {obj.CompileName}.@{fieldName}).Returns( ");
      wr.Append(compiler.TrExpr(binaryExpr.E1, false, wStmts));
      wr.WriteLine(");");
      return;
    }
    if (binaryExpr.E0 is not ApplySuffix applySuffix) {
      throw new NotImplementedException();
    }
    SynthesizeExpression(wr, applySuffix, wStmts);
    wr.Write(".Returns(");
    wr.Write("(");
    for (int i = 0; i < applySuffix.Args.Count; i++) {
      var arg = applySuffix.Args[i];
      var typeName = compiler.TypeName(arg.Type, wr, arg.tok);
      var bound = GetBound(arg);
      if (bound != null) {
        wr.Format($"{typeName} {bound.Item1.CompileName}");
      } else {
        // if the argument is not a bound variable, it is irrelevant to the
        // expression in the lambda
        wr.Format($"{typeName} _");
      }
      if (i != applySuffix.Args.Count - 1) {
        wr.Write(", ");
      }
    }
    wr.Write(")=>");
    wr.Append(compiler.TrExpr(binaryExpr.E1, false, wStmts));
    wr.WriteLine(");");
  }

  private void SynthesizeExpression(ConcreteSyntaxTree wr, ForallExpr forallExpr, ConcreteSyntaxTree wStmts) {
    if (forallExpr.Term is not BinaryExpr binaryExpr) {
      throw new NotImplementedException();
    }
    var declarations = new List<string>();

    // a MultiMatcher is created to convert an antecedent of the implication
    // following the forall statement to argument matching calls in Moq
    var matcherName = compiler.idGenerator.FreshId("matcher");

    var tmpId = compiler.idGenerator.FreshId("tmp");
    for (int i = 0; i < forallExpr.BoundVars.Count; i++) {
      var boundVar = forallExpr.BoundVars[i];
      var varType = compiler.TypeName(boundVar.Type, wr, boundVar.tok);
      bounds[boundVar] = $"It.Is<{varType}>(x => {matcherName}.Match(x))";
      declarations.Add($"var {boundVar.CompileName} = ({varType}) {tmpId}[{i}];");
    }

    wr.WriteLine($"var {matcherName} = new Dafny.MultiMatcher({declarations.Count}, {tmpId} => {{");
    foreach (var declaration in declarations) {
      wr.WriteLine($"\t{declaration}");
    }

    switch (binaryExpr.Op) {
      case BinaryExpr.Opcode.Imp:
        wr.Write("\treturn ");
        wr.Append(compiler.TrExpr(binaryExpr.E0, false, wStmts));
        wr.WriteLine(";");
        binaryExpr = (BinaryExpr)binaryExpr.E1;
        break;
      case BinaryExpr.Opcode.Eq:
        wr.WriteLine("\treturn true;");
        break;
      default:
        throw new NotImplementedException();
    }
    wr.WriteLine("});");
    SynthesizeExpression(wr, binaryExpr, wStmts);
  }

  /// <summary>
  /// Adds MultiMatcher class to the specified ConcreteSyntaxTree.
  /// MultiMatcher allows converting one expression over many arguments
  /// (like ones one finds in Dafny in antecedent of a forall statement)
  /// to many separate predicates over each argument (which is how argument
  /// matching is done in expressionC#'s Moq library)
  /// So, for instance, a Dafny postcondition
  ///   forall a,b:int :: a > b ==> o.m(a, b) == 4
  /// is converted to:
  /// 
  ///   var matcher = new Dafny.MultiMatcher(2, args => {
  ///     return args[0] > args[1];
  ///   });
  ///   o.Setup(x => x.m(It.Is<int>(a => matcher.Match(a)),
  ///                    It.Is<int>(b => matcher.Match(b)))).Returns(4);
  /// 
  /// </summary>
  internal static void EmitMultiMatcher(ConcreteSyntaxTree dafnyNamespace) {
    const string multiMatcher = @"
    class MultiMatcher {

      private readonly Func<object[], bool> predicate;
      private readonly int argumentCount;
      private readonly List<object> collectedArguments;

      public MultiMatcher(int argumentCount, Func<object[], bool> predicate) {
        this.predicate = predicate;
        this.argumentCount = argumentCount;
        collectedArguments = new();
      }

      public bool Match(object argument) {
        collectedArguments.Add(argument);
        if (collectedArguments.Count != argumentCount) {
          return true;
        }
        bool result = predicate(collectedArguments.ToArray());
        collectedArguments.Clear();
        return result;
      }
    }";
    var memberDeclaration = SyntaxFactory.ParseMemberDeclaration(multiMatcher);
    dafnyNamespace.WriteLine(memberDeclaration.ToFullString());
  }

  internal static void EmitImports(ConcreteSyntaxTree wr) {
    wr.WriteLine("using Moq;");
    wr.WriteLine("using System.Collections.Generic;");
  }
}
