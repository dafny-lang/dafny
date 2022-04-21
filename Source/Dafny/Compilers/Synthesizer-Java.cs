using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;

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
///           | EQUALS && EQUALS
/// FORALL    = forall BOUNDVARS :: EXPR ==> EQUALS
/// ARGLIST   = ID   // this can be one of the bound variables
///           | EXPR // this expr may not reference any of the bound variables 
///           | ARGLIST, ARGLIST
/// BOUNDVARS = ID : ID 
///           | BOUNDVARS, BOUNDVARS
/// 
/// </summary>
public class JavaSynthesizer {

  private readonly JavaCompiler compiler;
  private readonly ConcreteSyntaxTree ErrorWriter;
  // maps identifiers to the names of the corresponding mock:
  private Dictionary<IVariable, string> objectToMockName = new();
  // associates a bound variable with the lambda passed to argument matcher
  private Dictionary<IVariable, string> bounds = new();
  private Method lastSynthesizedMethod = null;

  public JavaSynthesizer(JavaCompiler compiler, ConcreteSyntaxTree errorWriter) {
    this.compiler = compiler;
    ErrorWriter = errorWriter;
  }

  /// <summary>
  /// Create a body for a method returning a fresh instance of an object 
  /// </summary>
  public ConcreteSyntaxTree CreateFreshMethod(Method m,
    ConcreteSyntaxTree wr) {
    var keywords = "public static ";
    var returnType = compiler.GetTargetReturnTypeReplacement(m, wr);
    wr = wr.NewBlock($"{keywords}{returnType} {m.CompileName}()");
    wr.FormatLine($"return new {returnType}();");
    return wr;
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
    wr = wr.NewBlock($"{keywords}{returnType} {compiler.PublicIdProtect(method.CompileName)}{typeParameters}({parameterString})");

    // Create the mocks:
    objectToMockName = method.Outs.ToDictionary(o => (IVariable)o,
      o => o.CompileName + "Mock");
    foreach (var (obj, mockName) in objectToMockName) {
      var typeName = compiler.TypeName(obj.Type, wr, obj.Tok);
      wr.FormatLine($"{returnType} {mockName} = org.mockito.Mockito.mock({returnType}.class);");
    }

    // Stub methods and fields according to the Dafny post-conditions:
    foreach (var ensureClause in method.Ens) {
      bounds = new();
      var wStmts = wr.Fork();
      SynthesizeExpression(wr, ensureClause.E, wStmts);
    }

    // Return the mocked objects:
    if (returnType != "void") {
      wr.FormatLine($"return {method.Outs[0].Name}Mock;");
    } else {
      foreach (var o in method.Outs) {
        wr.FormatLine($"{objectToReturnName[o]} = {method.Outs[0].Name}Mock;");
      }
    }
    // wr.WriteLine("}");
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

  private void SynthesizeExpression(ConcreteSyntaxTree wr, Expression expr, ConcreteSyntaxTree wStmts) {
    switch (expr) {
      case LiteralExpr literalExpr:
        compiler.TrExpr(literalExpr, wr, false, wStmts);
        break;
      case ApplySuffix applySuffix:
        SynthesizeExpression(wr, applySuffix, wStmts);
        break;
      case BinaryExpr binaryExpr:
        SynthesizeExpression(wr, binaryExpr, wStmts);
        break;
      case ForallExpr forallExpr:
        SynthesizeExpression(wr, forallExpr, wStmts);
        break;
      case FreshExpr:
        break;
      default:
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

    wr.Format($"org.mockito.Mockito.when({objectToMockName[receiver]}.{methodName}(");

    // The remaining part of the method uses Moq's argument matching to
    // describe the arguments for which the method should be stubbed
    // (in Dafny, this condition is the antecedent over bound variables)
    for (int i = 0; i < applySuffix.Args.Count; i++) {
      var arg = applySuffix.Args[i];
      var bound = GetBound(arg);
      if (bound != null) { // if true, arg is a bound variable
        wr.Write(bound.Item2);
      } else {
        compiler.TrExpr(arg, wr, false, wStmts);
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
      SynthesizeExpression(wr, binaryExpr.E0, wStmts);
      bounds = oldBounds;
      SynthesizeExpression(wr, binaryExpr.E1, wStmts);
      return;
    }
    if (binaryExpr.Op != BinaryExpr.Opcode.Eq) {
      throw new NotImplementedException();
    }
    if (binaryExpr.E0 is not ApplySuffix applySuffix) {
      throw new NotImplementedException();
    }
    SynthesizeExpression(wr, applySuffix, wStmts);
    wr.Write(".thenReturn(");
    compiler.TrExpr(binaryExpr.E1, wr, false, wStmts);
    wr.WriteLine(");");
  }

  private void SynthesizeExpression(ConcreteSyntaxTree wr, ForallExpr forallExpr, ConcreteSyntaxTree wStmts) {
    if (forallExpr.Term is not BinaryExpr binaryExpr) {
      throw new NotImplementedException();
    }

    var tmpId = compiler.idGenerator.FreshId("tmp");
    for (int i = 0; i < forallExpr.BoundVars.Count; i++) {
      var boundVar = forallExpr.BoundVars[i];
      var varType = compiler.TypeName(boundVar.Type, wr, boundVar.tok);
      bounds[boundVar] = $"org.mockito.Mockito.any({varType}.class)";
    }
    SynthesizeExpression(wr, binaryExpr, wStmts);
  }
}
