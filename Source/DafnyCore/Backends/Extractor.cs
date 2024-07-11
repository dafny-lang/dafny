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
using System.IO;
using System.Diagnostics.Contracts;
using DafnyCore;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GeneratorErrors;

namespace Microsoft.Dafny.Compilers {
  public class Extractor : ASTVisitor<IASTVisitorContext> {
    public static Boogie.Program Extract(Program program) {
      var extractor = new Extractor();
      extractor.VisitDeclarations(program.DefaultModule.Signature.TopLevels.Values.ToList());
      extractor.FixUpUsedByInformation();
      return extractor.extractedProgram;
    }

    private readonly Boogie.Program extractedProgram = new();
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

    protected override void VisitOneDeclaration(TopLevelDecl decl) {
      if (decl is ModuleDecl moduleDecl) {
        // TODO: look for {:extract} attribute on module
        VisitDeclarations(moduleDecl.Signature.TopLevels.Values.ToList());
        return;
      }

      if (GetExtractName(decl.Attributes) is { } extractName) {
        var ty = new Boogie.TypeCtorDecl(decl.tok, extractName, decl.TypeArgs.Count);
        extractedProgram.AddTopLevelDeclaration(ty);
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

      Boogie.Trigger? triggers = null;
      Contract.Assert(boundVars.Count != 0 || patterns == null);
      for (var i = patterns == null ? 0 : patterns.Count; 0 <= --i;) {
        var terms = patterns![i].ConvertAll(ExtractExpr);
        triggers = new Boogie.Trigger(tok, true, terms, triggers);
      }

      var ante = BoogieGenerator.BplAnd(lemma.Req.ConvertAll(req => ExtractExpr(req.E)));
      var post = BoogieGenerator.BplAnd(lemma.Ens.ConvertAll(ens => ExtractExpr(ens.E)));
      var body = BoogieGenerator.BplImp(ante, post);

      Boogie.QKeyValue kv = null;
      var extractAttributes = Attributes.FindAllExpressions(lemma.Attributes, "extract_attribute");
      Contract.Assert(boundVars.Count != 0 || extractAttributes == null);
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

      var axiomBody = boundVars.Count == 0 ? body : new Boogie.ForallExpr(tok, new List<TypeVariable>(), boundVars, kv, triggers, body);
      var axiom = new Boogie.Axiom(tok, axiomBody, $"axiom generated from lemma {method.Name}");
      extractedProgram.AddTopLevelDeclaration(axiom);

      if (usedByInfo != null) {
        Contract.Assert(usedByInfo.Args.Count == 1);
        var argument = (MemberSelectExpr)usedByInfo.Args[0].Resolved; // TODO: do error checking
        var function = (Function)argument.Member; // TODO: do error checking
        axiomUsedBy.Add((axiom, function));
      }
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
        extractedProgram.AddTopLevelDeclaration(fn);
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
      return Boogie.Expr.True;
    }
  }
}
