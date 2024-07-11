//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#nullable enable

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Compilers {
  public class Extractor : ASTVisitor<IASTVisitorContext> {
    public static Boogie.Program Extract(Program program) {
      var extractor = new Extractor();
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

    private Extractor() {
    }

    void FixUpUsedByInformation() {
      foreach (var (axiom, function) in axiomUsedBy) {
        var boogieFunction = functionExtractions[function]; // TODO: do error checking
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
      if (patterns == null & usedByInfo == null) {
        return;
      }

      Contract.Assert(lemma.TypeArgs.Count == 0); // TODO: fail more gently
      Contract.Assert(lemma.Outs.Count == 0); // TODO: fail more gently

      var tok = lemma.tok;

      var boundVars = lemma.Ins.ConvertAll(formal =>
        (Boogie.Variable)new Boogie.BoundVariable(tok, new TypedIdent(tok, formal.Name, ExtractType(formal.Type)))
      );

      var triggers = GetTriggers(tok, boundVars, patterns);

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
        Contract.Assert(usedByInfo.Args.Count == 1);
        var argument = (MemberSelectExpr)usedByInfo.Args[0].Resolved; // TODO: do error checking
        var function = (Function)argument.Member; // TODO: do error checking
        axiomUsedBy.Add((axiom, function));
      }
    }

    private Trigger? GetTriggers(IToken tok, List<Variable> boundVars, List<List<Expression>>? patterns) {
      Boogie.Trigger? triggers = null;
      Contract.Assert(boundVars.Count != 0 || patterns == null);
      for (var i = patterns == null ? 0 : patterns.Count; 0 <= --i;) {
        var terms = patterns![i].ConvertAll(ExtractExpr);
        triggers = new Boogie.Trigger(tok, true, terms, triggers);
      }

      return triggers;
    }

    private QKeyValue? GetKeyValues(IToken tok, Attributes attributes) {
      Boogie.QKeyValue kv = null;
      var extractAttributes = Attributes.FindAllExpressions(attributes, "extract_attribute");
      if (extractAttributes != null) {
        for (var i = extractAttributes.Count; 0 <= --i;) {
          string? attrName = null;
          var parameters = new List<object>();
          foreach (var argument in extractAttributes[i]) {
            if (attrName == null) {
              attrName = (string)((StringLiteralExpr)argument).Value; // TODO: do error checking
            } else {
              parameters.Add(ExtractExpr(argument));
            }
          }

          Contract.Assert(attrName != null); // TODO: fail more gently
          kv = new Boogie.QKeyValue(tok, attrName, parameters, kv);
        }
      }

      return kv;
    }

    public override void VisitFunction(Function function) {
      if (GetExtractName(function.Attributes) is { } extractName) {
        var tok = function.tok;
        Contract.Assert(function.TypeArgs.Count == 0); // TODO: throw an exception or something more gentle
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
      if (type is IntType) {
        return Boogie.Type.Int;
      } else if (type is BoolType) {
        return Boogie.Type.Bool;
      } else if (type is UserDefinedType udt) {
        var cl = udt.ResolvedClass;
        var name = GetExtractName(cl.Attributes) ?? cl.Name;
        return new Boogie.UnresolvedTypeIdentifier(Boogie.Token.NoToken, name, udt.TypeArgs.ConvertAll(ExtractType));
      } else {
        Contract.Assert(false); // TODO: fail more gently
        return null; // to please compiler
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
              return new Boogie.LiteralExpr(tok, boolValue);
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

        case UnaryOpExpr unaryOpExpr: {
            Contract.Assert(unaryOpExpr.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot); // TODO: fail more gently
            var e = ExtractExpr(unaryOpExpr.E);
            return Boogie.Expr.Not(e);
          }

        case QuantifierExpr quantifierExpr: {
            // TODO: look for :extract_pattern

            var boundVars = quantifierExpr.BoundVars.ConvertAll(boundVar =>
              (Boogie.Variable)new Boogie.BoundVariable(tok, new TypedIdent(tok, boundVar.Name, ExtractType(boundVar.Type)))
            );

            var patterns = Attributes.FindAllExpressions(quantifierExpr.Attributes, "extract_pattern");
            Contract.Assert(patterns.Count != 0); // don't support pattern-less quantifiers // TODO: fail more gracefully
            var triggers = GetTriggers(tok, boundVars, patterns);

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
      Contract.Assert(false, $"ExtractExpr TODO: {expr.GetType()}: {expr}"); // TODO: fail more gently
      return Boogie.Expr.True;
    }
  }
}
