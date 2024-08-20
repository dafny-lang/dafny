//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Compilers {
  public class ExtractorError : Exception {
    public ExtractorError(string message)
      : base(message) {
    }
  }

  public class BoogieExtractor : ASTVisitor<IASTVisitorContext> {
    /// <summary>
    /// Throws an "ExtractorError" if the input is unexpected or unsupported.
    /// </summary>
    public static Boogie.Program Extract(Program program) {
      var extractor = new BoogieExtractor();
      extractor.VisitModule(program.DefaultModule);
      extractor.FixUpUsedByInformation();

      var extractedProgram = new Boogie.Program();
      extractedProgram.AddTopLevelDeclarations(extractor.allDeclarations);
      return extractedProgram;
    }

    private List<Boogie.Declaration> declarations = new(); // for the current module
    private List<Boogie.Declaration> allDeclarations = new(); // these are the declarations for all modules marked with {:extract} 
    private readonly Dictionary<Function, Boogie.Function> functionExtractions = new();
    private readonly List<(Boogie.Axiom, Function)> axiomUsedBy = new();

    private BoogieExtractor() {
    }

    void FixUpUsedByInformation() {
      foreach (var (axiom, function) in axiomUsedBy) {
        if (!functionExtractions.TryGetValue(function, out var boogieFunction)) {
          throw new ExtractorError($":extract_used_by attribute mentions non-extracted function: {function.Name}");
        }
        boogieFunction.OtherDefinitionAxioms.Add(axiom);
      }
      axiomUsedBy.Clear();
    }

    public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
      return astVisitorContext;
    }

    void VisitModule(ModuleDecl module) {
      var previousDeclarations = declarations;
      declarations = new();

      VisitDeclarations(module.Signature.TopLevels.Values.ToList());

      if (Attributes.Contains(module.Signature.ModuleDef.Attributes, "extract")) {
        declarations.Sort((d0, d1) => d0.tok.pos - d1.tok.pos);
        allDeclarations.AddRange(declarations);
      }
      declarations = previousDeclarations;
    }

    protected override void VisitOneDeclaration(TopLevelDecl decl) {
      if (decl is ModuleDecl moduleDecl) {
        VisitModule(moduleDecl);
        return;
      }

      if (GetExtractName(decl.Attributes) is { } extractName) {
        var ty = new Boogie.TypeCtorDecl(decl.tok, extractName, decl.TypeArgs.Count);
        declarations.Add(ty);
      }

      base.VisitOneDeclaration(decl); // this will visit the declaration's members
    }

    public override void VisitMethod(Method method) {
      if (method is not Lemma lemma) {
        return;
      }

      var patterns = Attributes.FindAllExpressions(lemma.Attributes, "extract_pattern");
      var usedByInfo = Attributes.Find(lemma.Attributes, "extract_used_by");
      if (patterns == null && usedByInfo == null) {
        return;
      }

      if ((lemma.Ins.Count == 0) != (patterns == null)) {
        throw new ExtractorError($"a parameterized lemma must specify at least one :extract_pattern: {lemma.Name}");
      }
      if (lemma.TypeArgs.Count != 0) {
        throw new ExtractorError($"an extracted lemma is not allowed to have type parameters: {lemma.Name}");
      }
      if (lemma.Outs.Count != 0) {
        throw new ExtractorError($"an extracted lemma is not allowed to have out-parameters: {lemma.Name}");
      }

      var tok = lemma.tok;

      var boundVars = lemma.Ins.ConvertAll(formal =>
        (Boogie.Variable)new Boogie.BoundVariable(tok, new TypedIdent(tok, formal.Name, ExtractType(formal.Type)))
      );

      var triggers = GetTriggers(tok, patterns);

      var ante = BoogieGenerator.BplAnd(lemma.Req.ConvertAll(req => ExtractExpr(req.E)));
      var post = BoogieGenerator.BplAnd(lemma.Ens.ConvertAll(ens => ExtractExpr(ens.E)));
      var body = BoogieGenerator.BplImp(ante, post);

      Boogie.Expr axiomBody;
      if (boundVars.Count == 0) {
        axiomBody = body;
      } else {
        var kv = GetKeyValues(tok, lemma.Attributes);
        axiomBody = new Boogie.ForallExpr(tok, new List<TypeVariable>(), boundVars, kv, triggers, body);
      }
      var axiom = new Boogie.Axiom(tok, axiomBody);
      declarations.Add(axiom);

      if (usedByInfo != null) {
        if (usedByInfo.Args.Count == 1 && usedByInfo.Args[0].Resolved is MemberSelectExpr { Member: Function function }) {
          axiomUsedBy.Add((axiom, function));
        } else {
          throw new ExtractorError($":extract_used_by argument on lemma '{lemma.Name}' is expected to be an extracted function");
        }
      }
    }

    private Trigger? GetTriggers(IToken tok, List<List<Expression>>? patterns) {
      if (patterns == null) {
        return null;
      }

      Boogie.Trigger? triggers = null;
      for (var i = 0; i < patterns.Count; i++) {
        var terms = patterns![i].ConvertAll(ExtractExpr);
        triggers = new Boogie.Trigger(tok, true, terms, triggers);
      }

      return triggers;
    }

    private QKeyValue? GetKeyValues(IToken tok, Attributes attributes) {
      Boogie.QKeyValue kv = null;
      var extractAttributes = Attributes.FindAllExpressions(attributes, "extract_attribute");
      if (extractAttributes != null) {
        if (extractAttributes.Count == 0) {
          throw new ExtractorError($"first argument to :extract_attribute is expected to be a literal string; got no arguments");
        }
        for (var i = extractAttributes.Count; 0 <= --i;) {
          string? attrName = null;
          var parameters = new List<object>();
          foreach (var argument in extractAttributes[i]) {
            if (attrName != null) {
              parameters.Add(ExtractExpr(argument));
            } else if (argument is StringLiteralExpr { Value: string name }) {
              attrName = name;
            } else {
              throw new ExtractorError($"first argument to :extract_attribute is expected to be a literal string; got: {argument}");
            }
          }

          kv = new Boogie.QKeyValue(tok, attrName, parameters, kv);
        }
      }

      return kv;
    }

    public override void VisitFunction(Function function) {
      if (GetExtractName(function.Attributes) is { } extractName) {
        var tok = function.tok;
        if (function.TypeArgs.Count != 0) {
          throw new ExtractorError($"an extracted function is not allowed to have type parameters: {function.Name}");
        }
        var inParams = function.Ins.ConvertAll(formal =>
          (Boogie.Variable)new Boogie.Formal(tok, new TypedIdent(tok, formal.Name, ExtractType(formal.Type)), true)
        );
        var result = new Boogie.Formal(tok, new TypedIdent(tok, TypedIdent.NoName, ExtractType(function.ResultType)), false);
        var fn = new Boogie.Function(tok, extractName, inParams, result);
        declarations.Add(fn);
        functionExtractions.Add(function, fn);
      }
    }

    private Boogie.Type ExtractType(Type type) {
      switch (type) {
        case IntType:
          return Boogie.Type.Int;
        case BoolType:
          return Boogie.Type.Bool;
        case UserDefinedType udt: {
            var cl = udt.ResolvedClass;
            var name = GetExtractName(cl.Attributes) ?? cl.Name;
            return new Boogie.UnresolvedTypeIdentifier(Boogie.Token.NoToken, name, udt.TypeArgs.ConvertAll(ExtractType));
          }
        default:
          throw new ExtractorError($"type not supported by extractor: {type}");
      }
    }

    private string? GetExtractName(Attributes attributes) {
      if (Attributes.Find(attributes, "extract_name") is { } extractNameAttribute) {
        if (extractNameAttribute.Args.Count == 1 && extractNameAttribute.Args[0] is StringLiteralExpr { Value: string extractName }) {
          return extractName;
        }
      }
      return null;
    }

    private Boogie.Expr ExtractExpr(Expression expr) {
      expr = expr.Resolved;
      var tok = expr.tok;
      switch (expr) {
        case LiteralExpr literalExpr: {
            if (literalExpr.Value is bool boolValue) {
              // use the specific literals, rather than Boogie.LiteralExpr(bool), in order for the
              // peephole optimizations to kick in
              return boolValue ? Boogie.Expr.True : Boogie.Expr.False;
            } else if (literalExpr.Value is BigInteger intValue) {
              var n = BigNum.FromBigInt(intValue);
              return Boogie.Expr.Literal(n);
            }
            break;
          }

        case IdentifierExpr identifierExpr:
          return new Boogie.IdentifierExpr(tok, identifierExpr.Name);

        case FunctionCallExpr functionCallExpr: {
            var function = functionCallExpr.Function;
            var functionName = GetExtractName(function.Attributes) ?? function.Name;
            Contract.Assert(function.IsStatic);
            var arguments = functionCallExpr.Args.ConvertAll(ExtractExpr);
            return new Boogie.NAryExpr(tok, new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, functionName)), arguments);
          }

        case BinaryExpr binaryExpr: {
            var e0 = ExtractExpr(binaryExpr.E0);
            var e1 = ExtractExpr(binaryExpr.E1);
            switch (binaryExpr.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.EqCommon:
                return Boogie.Expr.Eq(e0, e1);
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                return Boogie.Expr.Neq(e0, e1);
              case BinaryExpr.ResolvedOpcode.Iff:
                return BoogieGenerator.BplIff(e0, e1);
              case BinaryExpr.ResolvedOpcode.Imp:
                return BoogieGenerator.BplImp(e0, e1);
              case BinaryExpr.ResolvedOpcode.And:
                return BoogieGenerator.BplAnd(e0, e1);
              case BinaryExpr.ResolvedOpcode.Or:
                return BoogieGenerator.BplOr(e0, e1);
              case BinaryExpr.ResolvedOpcode.Le:
                return Boogie.Expr.Le(e0, e1);
              case BinaryExpr.ResolvedOpcode.Lt:
                return Boogie.Expr.Lt(e0, e1);
              case BinaryExpr.ResolvedOpcode.Add:
                return Boogie.Expr.Add(e0, e1);
              case BinaryExpr.ResolvedOpcode.Sub:
                return Boogie.Expr.Sub(e0, e1);
              default:
                break;
            }
            break;
          }

        case UnaryOpExpr unaryOpExpr:
          if (unaryOpExpr.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot) {
            var e = ExtractExpr(unaryOpExpr.E);
            return Boogie.Expr.Not(e);
          } else {
            throw new ExtractorError($"extractor does not support unary operator {unaryOpExpr.ResolvedOp}");
          }

        case QuantifierExpr quantifierExpr: {
            var boundVars = quantifierExpr.BoundVars.ConvertAll(boundVar =>
              (Boogie.Variable)new Boogie.BoundVariable(tok, new TypedIdent(tok, boundVar.Name, ExtractType(boundVar.Type)))
            );

            var patterns = Attributes.FindAllExpressions(quantifierExpr.Attributes, "extract_pattern");
            if (patterns.Count == 0) {
              throw new ExtractorError("extraction expects every quantifier to specify at least one :extract_pattern");
            }
            var triggers = GetTriggers(tok, patterns);

            var kv = GetKeyValues(tok, quantifierExpr.Attributes);
            var body = ExtractExpr(quantifierExpr.LogicalBody());
            if (quantifierExpr is ExistsExpr) {
              return new Boogie.ExistsExpr(tok, new List<TypeVariable>(), boundVars, kv, triggers, body);
            } else {
              Contract.Assert(quantifierExpr is ForallExpr);
              return new Boogie.ForallExpr(tok, new List<TypeVariable>(), boundVars, kv, triggers, body);
            }
          }

        default:
          break;
      }

      throw new ExtractorError($"extraction does not support expression of type {expr.GetType()}: {expr}");
    }
  }
}
