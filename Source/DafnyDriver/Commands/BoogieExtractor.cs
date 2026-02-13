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
    public readonly IToken Tok;
    public ExtractorError(IToken tok, string message)
      : base(message) {
      Tok = tok;
    }
  }

  public class BoogieExtractor : ASTVisitor<IASTVisitorContext> {
    /// <summary>
    /// Says to look inside the module for contents to extract.
    /// Can be applied to a module.
    /// 
    /// Note: This attribute isn't used yet, so the use of the attribute is just a stylistic thing at the moment.
    /// Similarly, one can imagine that the extractor will look at a module's export clauses, to--in some way--check that
    /// the set of Boogie declarations exported are self consistent. But that isn't done yet, either. Instead, all contents
    /// of all files given to the extractor are considered for extraction.  
    /// </summary>
    private const string ExtractAttribute = "extract_boogie";

    /// <summary>
    /// Gives the Boogie name to be used in the extraction.
    /// Can be applied to types and functions.
    /// </summary>
    private const string NameAttribute = "extract_boogie_name";

    /// <summary>
    /// Says to place the extracted axiom declaration in the "uses" block of the given function.
    /// Can be applied to lemmas.
    /// </summary>
    private const string UsedByAttribute = "extract_used_by";

    /// <summary>
    /// Gives a matching pattern to be applied in the quantifier emitted from a lemma or from a quantifier.
    /// Can be applied to lemmas and quantifiers.
    /// </summary>
    private const string PatternAttribute = "extract_pattern";

    /// <summary>
    /// Specifies an additional attribute to be attached to the quantifier emitted from a lemma.
    /// Can be applied to lemmas.
    /// </summary>
    private const string AttributeAttribute = "extract_attribute";

    /// <summary>
    /// Throws an "ExtractorError" if the input is unexpected or unsupported.
    /// </summary>
    public static Boogie.Program Extract(Program program, string sourceModuleName) {
      var extractor = new BoogieExtractor(sourceModuleName);
      extractor.VisitModule(program.DefaultModule);
      extractor.FixUpUsedByInformation();

      var extractedProgram = new Boogie.Program();
      extractedProgram.AddTopLevelDeclarations(extractor.allDeclarations);
      return extractedProgram;
    }

    private readonly string SourceModuleName;
    private List<Boogie.Declaration> declarations = []; // for the current module
    private List<Boogie.Declaration> allDeclarations = []; // these are the declarations for all modules selected for extraction 
    private readonly Dictionary<Function, Boogie.Function> functionExtractions = new();
    private readonly List<(IToken, Boogie.Axiom, Function)> axiomUsedBy = [];

    private BoogieExtractor(string sourceModuleName) {
      SourceModuleName = sourceModuleName;
    }

    void FixUpUsedByInformation() {
      foreach (var (tok, axiom, function) in axiomUsedBy) {
        if (!functionExtractions.TryGetValue(function, out var boogieFunction)) {
          throw new ExtractorError(tok, $":{UsedByAttribute} attribute mentions non-extracted function: {function.Name}");
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
      declarations = [];

      VisitDeclarations(module.Signature.TopLevels.Values.ToList());

      if (Attributes.Contains(module.Signature.ModuleDef.Attributes, ExtractAttribute)) {
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

      if (decl.EnclosingModuleDefinition.Name != SourceModuleName) {
        // ignore this declaration
        return;
      }

      if (GetExtractName(decl.Attributes) is { } extractName) {
        var ty = new Boogie.TypeCtorDecl(decl.Origin, extractName, decl.TypeArgs.Count);
        declarations.Add(ty);
      }

      base.VisitOneDeclaration(decl); // this will visit the declaration's members
    }

    public override void VisitMethod(MethodOrConstructor method) {
      if (method is not Lemma lemma) {
        return;
      }

      var patterns = Attributes.FindAllExpressions(lemma.Attributes, PatternAttribute);
      var usedByInfo = Attributes.Find(lemma.Attributes, UsedByAttribute);
      if (patterns == null && usedByInfo == null) {
        return;
      }

      if ((lemma.Ins.Count == 0) != (patterns == null)) {
        throw new ExtractorError(lemma.Origin, $"a parameterized lemma must specify at least one :{PatternAttribute}: {lemma.Name}");
      }
      if (lemma.TypeArgs.Count != 0) {
        throw new ExtractorError(lemma.Origin, $"an extracted lemma is not allowed to have type parameters: {lemma.Name}");
      }
      if (lemma.Outs.Count != 0) {
        throw new ExtractorError(lemma.Origin, $"an extracted lemma is not allowed to have out-parameters: {lemma.Name}");
      }

      var tok = lemma.Origin;

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
        axiomBody = new Boogie.ForallExpr(tok, [], boundVars, kv, triggers, body);
      }
      var axiom = new Boogie.Axiom(tok, axiomBody);
      declarations.Add(axiom);

      if (usedByInfo != null) {
        if (usedByInfo.Args.Count == 1 && usedByInfo.Args[0].Resolved is MemberSelectExpr { Member: Function function }) {
          axiomUsedBy.Add((usedByInfo.Origin, axiom, function));
        } else {
          throw new ExtractorError(usedByInfo.Origin, $":{UsedByAttribute} argument on lemma '{lemma.Name}' is expected to be an extracted function");
        }
      }
    }

    private Trigger? GetTriggers(IOrigin tok, List<List<Expression>>? patterns) {
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

    private QKeyValue? GetKeyValues(IOrigin tok, Attributes? attributes) {
      QKeyValue? kv = null;
      var extractAttributes = Attributes.FindAllExpressions(attributes, AttributeAttribute);
      if (extractAttributes == null) {
        return kv;
      }

      if (extractAttributes.Count == 0) {
        throw new ExtractorError(tok, $"first argument to :{AttributeAttribute} is expected to be a literal string; got no arguments");
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
            throw new ExtractorError(tok, $"first argument to :{AttributeAttribute} is expected to be a literal string; got: {argument}");
          }
        }

        kv = new QKeyValue(tok, attrName, parameters, kv);
      }

      return kv;
    }

    public override void VisitFunction(Function function) {
      if (GetExtractName(function.Attributes) is { } extractName) {
        var tok = function.Origin;
        if (function.TypeArgs.Count != 0) {
          throw new ExtractorError(tok, $"an extracted function is not allowed to have type parameters: {function.Name}");
        }
        var inParams = function.Ins.ConvertAll(formal =>
          (Boogie.Variable)new Boogie.Formal(tok, new TypedIdent(tok, formal.Name, ExtractType(formal.Type)), true)
        );
        var result = new Boogie.Formal(tok, new TypedIdent(tok, TypedIdent.NoName, ExtractType(function.ResultType)), false);
        var fn = new Boogie.Function(tok, extractName, inParams, result);
        if (extractName is not ("[]" or "[:=]")) {
          declarations.Add(fn);
          functionExtractions.Add(function, fn);
        }
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
          throw new ExtractorError(type.Origin, $"type not supported by extractor: {type}");
      }
    }

    private string? GetExtractName(Attributes? attributes) {
      if (Attributes.Find(attributes, NameAttribute) is { } extractNameAttribute) {
        if (extractNameAttribute.Args.Count == 1 && extractNameAttribute.Args[0] is StringLiteralExpr { Value: string extractName }) {
          return extractName;
        }
      }
      return null;
    }

    private Boogie.Expr ExtractExpr(Expression expr) {
      expr = expr.Resolved;
      var tok = expr.Origin;
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
            if (functionName == "[]") {
              if (functionCallExpr.Args.Count != 2) {
                throw new ExtractorError(tok, $"function {functionName} expects 2 arguments, got {functionCallExpr.Args.Count}");
              }
              return Boogie.Expr.SelectTok(tok, ExtractExpr(functionCallExpr.Args[0]), ExtractExpr(functionCallExpr.Args[1]));
            } else if (functionName == "[:=]") {
              if (functionCallExpr.Args.Count != 3) {
                throw new ExtractorError(tok, $"function {functionName} expects 3 arguments, got {functionCallExpr.Args.Count}");
              }
              return Boogie.Expr.StoreTok(tok, ExtractExpr(functionCallExpr.Args[0]),
                ExtractExpr(functionCallExpr.Args[1]), ExtractExpr(functionCallExpr.Args[2]));
            } else {
              var arguments = functionCallExpr.Args.ConvertAll(ExtractExpr);
              return new Boogie.NAryExpr(tok, new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, functionName)), arguments);
            }
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
              case BinaryExpr.ResolvedOpcode.Mul:
                return Boogie.Expr.Mul(e0, e1);
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
            throw new ExtractorError(unaryOpExpr.Origin, $"extractor does not support unary operator {unaryOpExpr.ResolvedOp}");
          }

        case QuantifierExpr quantifierExpr: {
            var boundVars = quantifierExpr.BoundVars.ConvertAll(boundVar =>
              (Boogie.Variable)new Boogie.BoundVariable(tok, new TypedIdent(tok, boundVar.Name, ExtractType(boundVar.Type)))
            );

            var patterns = Attributes.FindAllExpressions(quantifierExpr.Attributes, PatternAttribute);
            if (patterns == null || patterns.Count == 0) {
              throw new ExtractorError(quantifierExpr.Origin, $"extraction expects every quantifier to specify at least one :{PatternAttribute}");
            }
            var triggers = GetTriggers(tok, patterns);

            var kv = GetKeyValues(tok, quantifierExpr.Attributes);
            var body = ExtractExpr(quantifierExpr.LogicalBody());
            if (quantifierExpr is ExistsExpr) {
              return new Boogie.ExistsExpr(tok, [], boundVars, kv, triggers, body);
            } else {
              Contract.Assert(quantifierExpr is ForallExpr);
              return new Boogie.ForallExpr(tok, [], boundVars, kv, triggers, body);
            }
          }

        default:
          break;
      }

      throw new ExtractorError(expr.Origin, $"extraction does not support expression of type {expr.GetType()}: {expr}");
    }
  }
}
