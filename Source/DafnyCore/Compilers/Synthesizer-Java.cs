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
public class JavaSynthesizer : Synthesizer {

  public JavaSynthesizer(JavaCompiler compiler, ConcreteSyntaxTree errorWriter) {
    this.compiler = compiler;
    this.errorWriter = errorWriter;
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
  /// Gets compiled to the following Java code:
  ///
  /// public static void CrossReferentialMock(out Even e1Return,
  ///                                         out Even e2Return) {
  ///     Even e1Mock = org.mockito.Mockito.spy(Even.class);
  ///     Even e1 = e1Mock;
  ///     Even e2Mock = org.mockito.Mockito.spy(Even.class);
  ///     Even e2 = e2Mock;
  ///     org.mockito.Mockito.when(e1.Next()).thenReturn(e2);
  ///     org.mockito.Mockito.when(e2.Next()).thenReturn(e1);
  ///     return new dafny.Tuple2<>(e1Mock, e2Mock);
  /// }
  /// </summary>
  public override ConcreteSyntaxTree SynthesizeMethod(Method method,
    List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody,
    ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {

    lastSynthesizedMethod = method;
    if (compiler is not JavaCompiler javaCompiler) {
      throw new Exception($"'{compiler}' is not of the type JavaCompiler"); 
    }
    
    // The following few lines are identical to those in Compiler.CreateMethod:
    var customReceiver = createBody &&
                         !forBodyInheritance &&
                         compiler.NeedsCustomReceiver(method);
    var keywords = javaCompiler.Keywords(true, true);
    var returnType = javaCompiler.GetTargetReturnTypeReplacement(method, wr);
    var typeParameters = javaCompiler.TypeParameters(SinglePassCompiler.TypeArgumentInstantiation.
      ToFormals(javaCompiler.ForTypeParameters(typeArgs, method, lookasideBody)));
    var parameters = javaCompiler
      .GetMethodParameters(method, typeArgs, lookasideBody, customReceiver, returnType);
    
    var parameterString = parameters.ToString();
    wr = wr.NewBlock($"{keywords}{returnType} {compiler.PublicIdProtect(method.CompileName)}{typeParameters}({parameterString})");

    // Create the mocks:
    objectToMockName = method.Outs.ToDictionary(o => (IVariable)o,
      o => o.CompileName + "Mock");
    string mockNames = null;
    foreach (var (obj, mockName) in objectToMockName) {
      var typeName = compiler.TypeName(obj.Type, wr, obj.Tok);
      wr.FormatLine($"{typeName} {mockName} = org.mockito.Mockito.spy({typeName}.class);");
      wr.FormatLine($"{typeName} {obj.CompileName} = {mockName};");
      mockNames = mockNames + mockName + ", ";
    }

    if (mockNames != null) {
      mockNames = mockNames.Remove(mockNames.Length - 2);
    }

    // Stub methods according to the Dafny post-conditions:
    foreach (var ensureClause in method.Ens) {
      bounds = new();
      var wStmts = wr.Fork();
      SynthesizeExpression(wr, ensureClause.E, wStmts);
    }

    // Return the mocked objects:
    wr.FormatLine(!returnType.Contains("Tuple")
      ? (FormattableString)$"return {method.Outs[0].Name}Mock;"
      : $"return new {returnType}<>({mockNames});");
    return wr;
  }

  protected override void SynthesizeExpression(ConcreteSyntaxTree wr, ApplySuffix applySuffix, ConcreteSyntaxTree wStmts) {

    var methodApp = (ExprDotName)applySuffix.Lhs;
    var receiver = ((IdentifierExpr)methodApp.Lhs.Resolved).Var;
    var method = ((MemberSelectExpr)methodApp.Resolved).Member;
    var methodName = method.CompileName;

    if (((Function)method).Ens.Count != 0) {
      compiler.Error(lastSynthesizedMethod.tok, "Post-conditions on function {0} might " +
                                 "be unsatisfied when synthesizing code " +
                                 "for method {1}", errorWriter,
        methodName, lastSynthesizedMethod.Name);
    }

    wr.Format($"org.mockito.Mockito.when({objectToMockName[receiver]}.{methodName}(");

    // The remaining part of the method uses Mockitos's argument matching to
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

  protected override void SynthesizeExpression(ConcreteSyntaxTree wr, BinaryExpr binaryExpr, ConcreteSyntaxTree wStmts) {
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

  protected override void SynthesizeExpression(ConcreteSyntaxTree wr, ForallExpr forallExpr, ConcreteSyntaxTree wStmts) {
    if (forallExpr.Term is not BinaryExpr binaryExpr) {
      throw new NotImplementedException();
    }
    
    foreach (var boundVar in forallExpr.BoundVars) {
      var varType = compiler.TypeName(boundVar.Type, wr, boundVar.tok);
      bounds[boundVar] = $"org.mockito.Mockito.any({varType}.class)";
    }
    SynthesizeExpression(wr, binaryExpr, wStmts);
  }
}