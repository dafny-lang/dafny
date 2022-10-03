using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Reactive;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class CompileNestedMatch {
  private ResolutionContext resolutionContext;
  private readonly Resolver resolver;

  private static HashSet<Program> ranOn = new();
  public CompileNestedMatch(Resolver resolver) {
    this.resolver = resolver;
  }

  public void Visit2(Program program) {
    if (!ranOn.Add(program)) {
      return;
    }
    
    ((INode) program).Visit(node => {
      if (node is ICallable callable) {
        resolutionContext = new ResolutionContext(callable, false);
      }
      ReflectiveUpdater.UpdateFieldsOfType<Statement>(node, stmt => {
        if (stmt is NestedMatchStmt nestedMatchStmt) {
          var compileNestedMatchStmt = CompileNestedMatchStmt(nestedMatchStmt);
          ResolveMatchStmt(compileNestedMatchStmt);
          return compileNestedMatchStmt;
        }
        return stmt;
      });
      
      ReflectiveUpdater.UpdateFieldsOfType<Expression>(node, expr => {
        if (expr is NestedMatchExpr nestedMatchExpr) {
          var compileNestedMatchExpr = CompileNestedMatchExpr(nestedMatchExpr);
          ResolveMatchExpr(compileNestedMatchExpr);
          return compileNestedMatchExpr;
        }
        return expr;
      });
      return true;
    });
    
    var tw = new StreamWriter("./debug.dfy");
    var pr = new Printer(tw, DafnyOptions.O.PrintMode);
    pr.PrintProgram(program, true);
    tw.Close();
  }
  
    void ResolveMatchStmt(MatchStmt s) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(s.OrigUnresolved == null);

      var dtd = s.Source.Type.AsDatatype;
      Dictionary<string, DatatypeCtor> ctors = dtd.ConstructorsByName;

      ISet<string> memberNamesUsed = new HashSet<string>();

      foreach (MatchCaseStmt mc in s.Cases) {
        if (ctors != null) {
          Contract.Assert(dtd != null);
          var ctorId = mc.Ctor.Name;
          if (s.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)s.Source.Type.AsDatatype;
            ctorId = BuiltIns.TupleTypeCtorName(tuple.Dims);
          }
          if (!ctors.ContainsKey(ctorId)) {
            // reporter.Error(MessageSource.Resolver, mc.tok, "member '{0}' does not exist in datatype '{1}'", ctorId, dtd.Name);
          } else {
            if (mc.Ctor.Formals.Count != mc.Arguments.Count) {
              if (s.Source.Type.AsDatatype is TupleTypeDecl) {
                // reporter.Error(MessageSource.Resolver, mc.tok, "case arguments count does not match source arguments count");
              } else {
                // reporter.Error(MessageSource.Resolver, mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", ctorId, mc.Arguments.Count, mc.Ctor.Formals.Count);
              }
            }
            if (memberNamesUsed.Contains(ctorId)) {
              // reporter.Error(MessageSource.Resolver, mc.tok, "member {0} appears in more than one case", mc.Ctor.Name);
            } else {
              memberNamesUsed.Add(ctorId);  // add mc.Id to the set of names used
            }
          }
        }
      }
      if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
        // We could complain about the syntactic omission of constructors:
        //   reporter.Error(MessageSource.Resolver, stmt, "match statement does not cover all constructors");
        // but instead we let the verifier do a semantic check.
        // So, for now, record the missing constructors:
        foreach (var ctr in dtd.Ctors) {
          if (!memberNamesUsed.Contains(ctr.Name)) {
            s.MissingCases.Add(ctr);
          }
        }
        Contract.Assert(memberNamesUsed.Count + s.MissingCases.Count == dtd.Ctors.Count);
      }
    }
    
    void ResolveMatchExpr(MatchExpr me) {
      Contract.Requires(me != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(me.OrigUnresolved == null);
      bool debug = DafnyOptions.O.MatchCompilerDebug;
      if (debug) {
        Console.WriteLine("DEBUG: {0} In ResolvedMatchExpr");
      }

      var dtd = me.Source.Type.AsDatatype;
      Dictionary<string, DatatypeCtor> ctors = dtd.ConstructorsByName;

      ISet<string> memberNamesUsed = new HashSet<string>();
      me.Type = new InferredTypeProxy();
      foreach (MatchCaseExpr mc in me.Cases) {
        if (ctors != null) {
          var ctorId = mc.Ctor.Name;
          if (me.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)me.Source.Type.AsDatatype;
            ctorId = BuiltIns.TupleTypeCtorName(tuple.Dims);
          }
          if (!ctors.ContainsKey(ctorId)) {
            // reporter.Error(MessageSource.Resolver, mc.tok, "member '{0}' does not exist in datatype '{1}'", ctorId, dtd.Name);
          } else {
            if (mc.Ctor.Formals.Count != mc.Arguments.Count) {
              if (me.Source.Type.AsDatatype is TupleTypeDecl) {
                // reporter.Error(MessageSource.Resolver, mc.tok, "case arguments count does not match source arguments count");
              } else {
                // reporter.Error(MessageSource.Resolver, mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", ctorId, mc.Arguments.Count, mc.Ctor.Formals.Count);
              }
            }
            if (memberNamesUsed.Contains(ctorId)) {
              // reporter.Error(MessageSource.Resolver, mc.tok, "member {0} appears in more than one case", mc.Ctor.Name);
            } else {
              memberNamesUsed.Add(ctorId);  // add mc.Id to the set of names used
            }
          }
        }
      }
      if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
        // We could complain about the syntactic omission of constructors:
        //   reporter.Error(MessageSource.Resolver, expr, "match expression does not cover all constructors");
        // but instead we let the verifier do a semantic check.
        // So, for now, record the missing constructors:
        foreach (var ctr in dtd.Ctors) {
          if (!memberNamesUsed.Contains(ctr.Name)) {
            me.MissingCases.Add(ctr);
          }
        }
        Contract.Assert(memberNamesUsed.Count + me.MissingCases.Count == dtd.Ctors.Count);
      }
      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolvedMatchExpr - DONE", me.tok.line);
      }
    }
  
  private MatchExpr CompileNestedMatchExpr(NestedMatchExpr e) {
    if (DafnyOptions.O.MatchCompilerDebug) {
      Console.WriteLine("DEBUG: CompileNestedMatchExpr for match at line {0}", e.tok.line);
    }

    var cases = e.Cases.SelectMany(FlattenNestedMatchCaseExpr).ToList();
    MatchTempInfo mti = new MatchTempInfo(e.Type, e.tok, cases.Count, resolutionContext, DafnyOptions.O.MatchCompilerDebug);

    // create Rbranches from MatchCaseExpr and set the branch tokens in mti
    List<RBranch> branches = new List<RBranch>();
    for (int id = 0; id < cases.Count; id++) {
      var branch = cases.ElementAt(id);
      branches.Add(new RBranchExpr(id, branch, branch.Attributes));
      mti.BranchTok[id] = branch.Tok;
    }

    List<Expression> matchees = new List<Expression>();
    matchees.Add(e.Source);
    SyntaxContainer rb = CompileRBranch(mti, new HoleCtx(), matchees, branches);
    if (rb is null) {
      // Happens only if the match has no cases, create a Match with no cases as resolved expression and let ResolveMatchExpr handle it.
      return new MatchExpr(e.tok, e.Source, new List<MatchCaseExpr>(), e.UsesOptionalBraces);
    } else if (rb is CExpr) {
      // replace e with desugared expression
      var newME = ((CExpr)rb).Body;
      for (int id = 0; id < mti.BranchIDCount.Length; id++) {
        if (mti.BranchIDCount[id] <= 0) {
          resolver.reporter.Warning(MessageSource.Resolver, mti.BranchTok[id], "this branch is redundant");
          resolver.scope.PushMarker();
          //CheckLinearNestedMatchCase(e.Source.Type, cases.ElementAt(id), resolutionContext);
          //ResolveExpression(cases.ElementAt(id).Body, resolutionContext);
          resolver.scope.PopMarker();
        }
      }
      return (MatchExpr) newME;
    } else {
      Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a CExpr
    }

    // if (DafnyOptions.O.MatchCompilerDebug) {
    //   Console.WriteLine("DEBUG: Done CompileNestedMatchExpr at line {0}", mti.Tok.line);
    // }

  }

  /// <summary>
  /// Stmt driver for CompileRBranch
  /// Input is an unresolved NestedMatchStmt with potentially nested, overlapping patterns
  /// On output, the NestedMatchStmt has field ResolvedStatement filled with semantically equivalent code
  /// </summary>
  private MatchStmt CompileNestedMatchStmt(NestedMatchStmt s) {

    if (DafnyOptions.O.MatchCompilerDebug) {
      Console.WriteLine("DEBUG: CompileNestedMatchStmt for match at line {0}", s.Tok.line);
    }

    var cases = s.Cases.SelectMany(FlattenNestedMatchCaseStmt).ToList();
    // initialize the MatchTempInfo to record position and duplication information about each branch
    MatchTempInfo mti = new MatchTempInfo(s.Tok, s.EndTok, cases.Count, resolutionContext.WithGhost(s.IsGhost), DafnyOptions.O.MatchCompilerDebug, s.Attributes);

    // create Rbranches from NestedMatchCaseStmt and set the branch tokens in mti
    List<RBranch> branches = new List<RBranch>();
    for (int id = 0; id < cases.Count; id++) {
      var branch = cases.ElementAt(id);
      branches.Add(new RBranchStmt(id, branch, branch.Attributes));
      mti.BranchTok[id] = branch.Tok;
    }
    List<Expression> matchees = new List<Expression>();
    matchees.Add(s.Source);
    SyntaxContainer rb = CompileRBranch(mti, new HoleCtx(), matchees, branches);
    if (rb is null) {
      // Happens only if the nested match has no cases, create a MatchStmt with no branches.
      return new MatchStmt(s.Tok, s.EndTok, s.Source, new List<MatchCaseStmt>(), s.UsesOptionalBraces, s.Attributes);
    } else if (rb is CStmt c) {
      // Resolve s as desugared match
      var result = c.Body;
      result.Attributes = s.Attributes;
      for (int id = 0; id < mti.BranchIDCount.Length; id++) {
        if (mti.BranchIDCount[id] <= 0) {
          resolver.reporter.Warning(MessageSource.Resolver, mti.BranchTok[id], "this branch is redundant");
          resolver.scope.PushMarker();
          // CheckLinearNestedMatchCase(s.Source.Type, cases.ElementAt(id), resolutionContext);
          // cases.ElementAt(id).Body.ForEach(s => ResolveStatement(s, resolutionContext));
          resolver.scope.PopMarker();
        }
      }

      return (MatchStmt)result;
    } else {
      Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a StmtContainer
    }

    // if (DafnyOptions.O.MatchCompilerDebug) {
    //   Console.WriteLine("DEBUG: Done CompileNestedMatchStmt at line {0}.", mti.Tok.line);
    // }
  }
  
  private IEnumerable<NestedMatchCaseStmt> FlattenNestedMatchCaseStmt(NestedMatchCaseStmt c) {
    foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
      yield return new NestedMatchCaseStmt(c.Tok, pat,
        c.Body,
        c.Attributes);
    }
  }

  private ExtendedPattern RemoveIllegalSubpatterns(ExtendedPattern pat, bool inDisjunctivePattern) {
    switch (pat) {
      case LitPattern:
        return pat;
      case IdPattern p:
        if (inDisjunctivePattern && p.ResolvedLit == null && p.Arguments == null && !p.IsWildcardPattern) {
          resolver.reporter.Error(MessageSource.Resolver, pat.Tok, "Disjunctive patterns may not bind variables");
          return new IdPattern(p.Tok, resolver.FreshTempVarName("_", null), null, p.IsGhost);
        }
        var args = p.Arguments?.ConvertAll(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern));
        return new IdPattern(p.Tok, p.Id, p.Type, args, p.IsGhost) { ResolvedLit = p.ResolvedLit, BoundVar = p.BoundVar };
      case DisjunctivePattern p:
        resolver.reporter.Error(MessageSource.Resolver, pat.Tok, "Disjunctive patterns are not allowed inside other patterns");
        return new IdPattern(p.Tok, resolver.FreshTempVarName("_", null), null, p.IsGhost);
      default:
        Contract.Assert(false);
        return null;
    }
  }

  private IEnumerable<ExtendedPattern> FlattenDisjunctivePatterns(ExtendedPattern pat) {
    // TODO: Once we rewrite the pattern-matching compiler, we'll handle disjunctive patterns in it, too.
    // For now, we handle top-level disjunctive patterns by duplicating the corresponding cases here, and disjunctive
    // sub-patterns are unsupported.
    return pat is DisjunctivePattern p
      ? p.Alternatives.ConvertAll(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern: true))
      : Enumerable.Repeat(RemoveIllegalSubpatterns(pat, inDisjunctivePattern: false), 1);
  }

  private IEnumerable<NestedMatchCaseExpr> FlattenNestedMatchCaseExpr(NestedMatchCaseExpr c) {
    foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
      yield return new NestedMatchCaseExpr(c.Tok, pat, c.Body, c.Attributes);
    }
  }
  
  // Assumes that all SyntaxContainers in blocks and def are of the same subclass
  private SyntaxContainer MakeIfFromContainers(MatchTempInfo mti, MatchingContext context, Expression matchee, List<Tuple<LiteralExpr, SyntaxContainer>> blocks, SyntaxContainer def) {

    if (blocks.Count == 0) {
      if (def is CStmt sdef) {
        // Ensures the statements are wrapped in braces
        return new CStmt(null, BlockStmtOfCStmt(sdef.Body.Tok, sdef.Body.EndTok, sdef));
      } else {
        return def;
      }
    }

    Tuple<LiteralExpr, SyntaxContainer> currBlock = blocks.First();
    blocks = blocks.Skip(1).ToList();

    IToken tok = matchee.tok;
    IToken endtok = matchee.tok;
    BinaryExpr guard = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, matchee, currBlock.Item1);
    guard.ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon;
    guard.Type = Type.Bool;

    var elsC = MakeIfFromContainers(mti, context, matchee, blocks, def);

    if (currBlock.Item2 is CExpr) {
      var item2 = (CExpr)currBlock.Item2;
      if (elsC is null) {
        // handle an empty default
        // assert guard; item2.Body
        var contextStr = context.FillHole(new IdCtx(string.Format("c: {0}", matchee.Type.ToString()), new List<MatchingContext>())).AbstractAllHoles().ToString();
        var errorMessage = new StringLiteralExpr(mti.Tok, string.Format("missing case in match expression: {0} (not all possibilities for constant 'c' in context have been covered)", contextStr), true);
        errorMessage.Type = new SeqType(Type.Char);
        var attr = new Attributes("error", new List<Expression>() { errorMessage }, null);
        var ag = new AssertStmt(mti.Tok, endtok, AutoGeneratedExpression.Create(guard, mti.Tok), null, null, attr);
        return new CExpr(null, new StmtExpr(tok, ag, item2.Body));
      } else {
        var els = (CExpr)elsC;
        return new CExpr(null, new ITEExpr(tok, false, guard, item2.Body, els.Body));
      }
    } else {
      var item2 = BlockStmtOfCStmt(tok, endtok, (CStmt)currBlock.Item2);
      if (elsC is null) {
        // handle an empty default
        // assert guard; item2.Body
        var contextStr = context.FillHole(new IdCtx(string.Format("c: {0}", matchee.Type.ToString()), new List<MatchingContext>())).AbstractAllHoles().ToString();
        var errorMessage = new StringLiteralExpr(mti.Tok, string.Format("missing case in match statement: {0} (not all possibilities for constant 'c' have been covered)", contextStr), true);
        errorMessage.Type = new SeqType(Type.Char);
        var attr = new Attributes("error", new List<Expression>() { errorMessage }, null);
        var ag = new AssertStmt(mti.Tok, endtok, AutoGeneratedExpression.Create(guard, mti.Tok), null, null, attr);
        var body = new List<Statement>();
        body.Add(ag);
        body.AddRange(item2.Body);
        return new CStmt(null, new BlockStmt(tok, endtok, body));
      } else {
        var els = (CStmt)elsC;
        return new CStmt(null, new IfStmt(tok, endtok, false, guard, item2, els.Body));
      }
    }
  }


  private MatchCase MakeMatchCaseFromContainer(IToken tok, KeyValuePair<string, DatatypeCtor> ctor, List<BoundVar> freshPatBV, SyntaxContainer insideContainer, bool FromBoundVar) {
    MatchCase newMatchCase;
    if (insideContainer is CStmt c) {
      List<Statement> insideBranch = UnboxStmtContainer(insideContainer);
      newMatchCase = new MatchCaseStmt(tok, ctor.Value, FromBoundVar, freshPatBV, insideBranch, c.Attributes);
    } else {
      var insideBranch = ((CExpr)insideContainer).Body;
      var attrs = ((CExpr)insideContainer).Attributes;
      newMatchCase = new MatchCaseExpr(tok, ctor.Value, FromBoundVar, freshPatBV, insideBranch, attrs);
    }
    newMatchCase.Ctor = ctor.Value;
    return newMatchCase;
  }

  private BoundVar CreatePatBV(IToken tok, Type type, ICodeContext codeContext) {
    var name = resolver.FreshTempVarName("_mcc#", codeContext);
    return new BoundVar(new AutoGeneratedToken(tok), name, type);
  }

  private IdPattern CreateFreshId(IToken tok, Type type, ICodeContext codeContext, bool isGhost = false) {
    var name = resolver.FreshTempVarName("_mcc#", codeContext);
    return new IdPattern(new AutoGeneratedToken(tok), name, type, null, isGhost);
  }

  private void PrintRBranches(MatchingContext context, List<Expression> matchees, List<RBranch> branches) {
    Console.WriteLine("\t=-------=");
    Console.WriteLine("\tCurrent context:");
    Console.WriteLine("\t> {0}", context.ToString());
    Console.WriteLine("\tCurrent matchees:");

    foreach (Expression matchee in matchees) {
      Console.WriteLine("\t> {0}", Printer.ExprToString(matchee));
    }
    Console.WriteLine("\tCurrent branches:");
    foreach (RBranch branch in branches) {
      Console.WriteLine(branch.ToString());
    }
    Console.WriteLine("\t-=======-");
  }

  /*
   * Implementation of case 3** (some of the head patterns are constants) of pattern-match compilation
   * PairPB contains, for each branches, its head pattern and the rest of the branch.
   */
  private SyntaxContainer CompileRBranchConstant(MatchTempInfo mti, MatchingContext context, Expression currMatchee, List<Expression> matchees, List<Tuple<ExtendedPattern, RBranch>> pairPB) {
    // Decrease the count for each branch (increases back for each occurence later on)
    foreach (var PB in pairPB) {
      mti.UpdateBranchID(PB.Item2.BranchID, -1);
    }

    // Create a list of alternatives
    List<LiteralExpr> alternatives = new List<LiteralExpr>();
    foreach (var PB in pairPB) {
      var pat = PB.Item1;
      LiteralExpr lit = null;
      if (pat is LitPattern lpat) {
        lit = lpat.OptimisticallyDesugaredLit;
      } else if (pat is IdPattern id && id.ResolvedLit != null) {
        lit = id.ResolvedLit;
      }

      lit.Type = currMatchee.Type;

      if (lit != null && !alternatives.Exists(x => object.Equals(x.Value, lit.Value))) {
        alternatives.Add(lit);
      }
    }

    List<Tuple<LiteralExpr, SyntaxContainer>> currBlocks = new List<Tuple<LiteralExpr, SyntaxContainer>>();
    // For each possible alternatives, filter potential cases and recur
    foreach (var currLit in alternatives) {
      List<RBranch> currBranches = new List<RBranch>();
      foreach (var PB in pairPB) {
        var pat = PB.Item1;
        LiteralExpr lit = null;
        if (pat is LitPattern lpat) {
          lit = lpat.OptimisticallyDesugaredLit;
        }

        if (pat is IdPattern id && id.ResolvedLit != null) {
          lit = id.ResolvedLit;
        }

        if (lit != null) {
          // if pattern matches the current alternative, add it to the branch for this case, otherwise ignore it
          if (object.Equals(lit.Value, currLit.Value)) {
            mti.UpdateBranchID(PB.Item2.BranchID, 1);
            currBranches.Add(CloneRBranch(PB.Item2));
          }
        } else if (pat is IdPattern currPattern) {
          // pattern is a bound variable, clone and let-bind the Lit
          var currBranch = CloneRBranch(PB.Item2);
          LetBindNonWildCard(currBranch, currPattern, currLit);
          mti.UpdateBranchID(PB.Item2.BranchID, 1);
          currBranches.Add(currBranch);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      }
      // Update the current context
      MatchingContext newcontext = context.FillHole(new LitCtx(currLit));

      // Recur on the current alternative
      var currBlock = CompileRBranch(mti, newcontext, matchees.Select(x => x).ToList(), currBranches);
      currBlocks.Add(new Tuple<LiteralExpr, SyntaxContainer>(currLit, currBlock));
    }
    // Create a default case
    List<RBranch> defaultBranches = new List<RBranch>();
    for (int i = 0; i < pairPB.Count; i++) {
      var PB = pairPB.ElementAt(i);
      if (PB.Item1 is IdPattern currPattern && currPattern.ResolvedLit == null && currPattern.Arguments == null) {
        // Pattern is a bound variable, clone and let-bind the Lit
        var currBranch = CloneRBranch(PB.Item2);
        LetBindNonWildCard(currBranch, currPattern, currMatchee);
        mti.UpdateBranchID(PB.Item2.BranchID, 1);
        defaultBranches.Add(currBranch);
      }
    }
    // defaultBranches.Count check is to avoid adding "missing branches" when default is not present
    SyntaxContainer defaultBlock = defaultBranches.Count == 0 ? null : CompileRBranch(mti, context.AbstractHole(), matchees.Select(x => x).ToList(), defaultBranches);

    // Create If-construct joining the alternatives
    var ifcon = MakeIfFromContainers(mti, context, currMatchee, currBlocks, defaultBlock);
    return ifcon;
  }

  /*
   * Implementation of case 3 (some of the head patterns are constructors) of pattern-match compilation
   * Current matchee is a datatype (with type parameter substitution in subst) with constructors in ctors
   * PairPB contains, for each branches, its head pattern and the rest of the branch.
   */
  private SyntaxContainer CompileRBranchConstructor(MatchTempInfo mti, MatchingContext context, Expression currMatchee, Dictionary<TypeParameter, Type> subst, Dictionary<string, DatatypeCtor> ctors, List<Expression> matchees, List<Tuple<ExtendedPattern, RBranch>> pairPB) {
    var newMatchCases = new List<MatchCase>();
    // Update mti -> each branch generates up to |ctors| copies of itself
    foreach (var PB in pairPB) {
      mti.UpdateBranchID(PB.Item2.BranchID, ctors.Count - 1);
    }

    var ctorToFromBoundVar = new HashSet<string>();

    foreach (var ctor in ctors) {
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[3]>>>> Ctor {0}", ctor.Key);
      }

      var currBranches = new List<RBranch>();

      // create a bound variable for each formal to use in the MatchCase for this constructor
      // using the currMatchee.tok to get a location closer to the error if something goes wrong
      var freshPatBV = ctor.Value.Formals.ConvertAll(
        x => CreatePatBV(currMatchee.tok, Resolver.SubstType(x.Type, subst), mti.CodeContext.CodeContext));

      // rhs to bind to head-patterns that are bound variables
      var rhsExpr = currMatchee;
      var ctorCounter = 0;

      // -- filter branches for each constructor
      for (int i = 0; i < pairPB.Count; i++) {
        var PB = pairPB.ElementAt(i);
        if (PB.Item1 is IdPattern currPattern) {
          if (ctor.Key.Equals(currPattern.Id) && currPattern.Arguments != null) {
            // ==[3.1]== If pattern is same constructor, push the arguments as patterns and add that branch to new match
            // After making sure the constructor is applied to the right number of arguments
            var currBranch = CloneRBranch(PB.Item2);
            if (!(currPattern.Arguments.Count.Equals(ctor.Value.Formals.Count))) {
              resolver.reporter.Error(MessageSource.Resolver, mti.BranchTok[PB.Item2.BranchID], "constructor {0} of arity {1} is applied to {2} argument(s)", ctor.Key, ctor.Value.Formals.Count, currPattern.Arguments.Count);
            }
            for (int j = 0; j < currPattern.Arguments.Count; j++) {
              // mark patterns standing in for ghost field
              currPattern.Arguments[j].IsGhost = currPattern.Arguments[j].IsGhost || ctor.Value.Formals[j].IsGhost;
            }
            currBranch.Patterns.InsertRange(0, currPattern.Arguments);
            currBranches.Add(currBranch);
            ctorCounter++;
          } else if (ctors.ContainsKey(currPattern.Id) && currPattern.Arguments != null) {
            // ==[3.2]== If the pattern is a different constructor, drop the branch
            mti.UpdateBranchID(PB.Item2.BranchID, -1);
          } else if (currPattern.ResolvedLit != null) {
            // TODO
          } else {
            // ==[3.3]== If the pattern is a bound variable, create new bound variables for each of the arguments of the constructor, and let-binds the matchee as original bound variable
            // n.b. this may duplicate the matchee

            // make sure this potential bound var is not applied to anything, in which case it is likely a mispelled constructor
            if (currPattern.Arguments != null && currPattern.Arguments.Count != 0) {
              resolver.reporter.Error(MessageSource.Resolver, mti.BranchTok[PB.Item2.BranchID], "bound variable {0} applied to {1} argument(s).", currPattern.Id, currPattern.Arguments.Count);
            }

            var currBranch = CloneRBranch(PB.Item2);

            List<IdPattern> freshArgs = ctor.Value.Formals.ConvertAll(x =>
              CreateFreshId(currPattern.Tok, Resolver.SubstType(x.Type, subst), mti.CodeContext.CodeContext, x.IsGhost));

            currBranch.Patterns.InsertRange(0, freshArgs);
            LetBindNonWildCard(currBranch, currPattern, rhsExpr);
            currBranches.Add(currBranch);
            ctorToFromBoundVar.Add(ctor.Key);
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      }
      // Add variables corresponding to the arguments of the current constructor (ctor) to the matchees
      List<IdentifierExpr> freshMatchees = freshPatBV.ConvertAll(x => new IdentifierExpr(x.tok, x));
      List<Expression> cmatchees = matchees.Select(x => x).ToList();
      cmatchees.InsertRange(0, freshMatchees);
      // Update the current context
      MatchingContext ctorctx = new IdCtx(ctor);
      MatchingContext newcontext = context.FillHole(ctorctx);
      var insideContainer = CompileRBranch(mti, newcontext, cmatchees, currBranches);
      if (insideContainer is null) {
        // If no branch matches this constructor, drop the case
        continue;
      } else {
        // Otherwise, add the case the new match created at [3]
        var tok = insideContainer.Tok is null ? new AutoGeneratedToken(currMatchee.tok) : insideContainer.Tok;
        var FromBoundVar = ctorToFromBoundVar.Contains(ctor.Key);
        MatchCase newMatchCase = MakeMatchCaseFromContainer(tok, ctor, freshPatBV, insideContainer, FromBoundVar);
        // newMatchCase.Attributes = (new Cloner()).CloneAttributes(mti.Attributes);
        newMatchCases.Add(newMatchCase);
      }
    }
    // Generate and pack the right kind of Match
    if (mti.isStmt) {
      var newMatchCaseStmts = newMatchCases.Select(x => (MatchCaseStmt)x).ToList();
      foreach (var c in newMatchCaseStmts) {
        if (Attributes.Contains(c.Attributes, "split")) {
          continue;
        }

        var args = new List<Expression>();
        var literalExpr = new LiteralExpr(mti.Tok, false);
        literalExpr.Type = Type.Bool;
        args.Add(literalExpr);
        c.Attributes = new Attributes("split", args, c.Attributes);
      }
      var newMatchStmt = new MatchStmt(mti.Tok, mti.EndTok, currMatchee, newMatchCaseStmts, true, mti.Attributes, context);
      newMatchStmt.IsGhost |= mti.CodeContext.IsGhost;
      return new CStmt(null, newMatchStmt);
    } else {
      var newMatchExpr = new MatchExpr(mti.Tok, currMatchee, newMatchCases.ConvertAll(x => (MatchCaseExpr)x), true, context);
      newMatchExpr.Type = mti.Type;
      return new CExpr(null, newMatchExpr);
    }
  }

  /// <summary>
  /// Create a decision tree with flattened MatchStmt (or MatchExpr) with disjoint cases and if-constructs
  /// Start with a list of n matchees and list of m branches, each with n patterns and a body
  /// 1 - if m = 0, then no original branch exists for the current case, return null
  /// 2 - if n = 0, return the body of the first branch
  /// 3** - if the head-matchee is a base type, but some patterns are constants, create if-else construct for one level and recur
  /// 3 - if some of the head-patterns are constructors (including tuples), create one level of matching at the type of the head-matchee,
  ///     recur for each constructor of that datatype
  /// 4 - Otherwise, all head-patterns are variables, let-bind the head-matchee as the head-pattern in each of the bodypatterns,
  ///     continue processing the matchees
  /// </summary>
  private SyntaxContainer CompileRBranch(MatchTempInfo mti, MatchingContext context, List<Expression> matchees, List<RBranch> branches) {
    if (mti.Debug) {
      Console.WriteLine("DEBUG: In CompileRBranch:");
      PrintRBranches(context, matchees, branches);
    }

    // For each branch, number of matchees (n) is the number of patterns held by the branch
    if (!branches.TrueForAll(x => matchees.Count == x.Patterns.Count)) {
      resolver.reporter.Error(MessageSource.Resolver, mti.Tok, "Match is malformed, make sure constructors are fully applied");
    }

    if (branches.Count == 0) {
      // ==[1]== If no branch, then match is not syntactically exhaustive -- return null
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[1]=== No Branch");
        Console.WriteLine("\t{0} Potential exhaustiveness failure on context: {1}", mti.Tok.line, context.AbstractAllHoles().ToString());
      }
      // (Semantics) exhaustiveness is checked by the verifier, so no need for a warning here
      // reporter.Warning(MessageSource.Resolver, mti.Tok, "non-exhaustive case-statement");
      return null;
    }

    if (matchees.Count == 0) {
      // ==[2]== No more matchee to process, return the first branch and decrement the count of dropped branches
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[2]=== No Matchee");
        Console.WriteLine("\treturn Bid:{0}", branches.First().BranchID);
      }

      for (int i = 1; i < branches.Count; i++) {
        mti.UpdateBranchID(branches.ElementAt(i).BranchID, -1);
      }
      return PackBody(mti.BranchTok[branches.First().BranchID], branches.First());
    }

    // Otherwise, start handling the first matchee
    Expression currMatchee = matchees.First();
    matchees = matchees.Skip(1).ToList();

    // Get the datatype of the matchee
    var currMatcheeType = resolver.PartiallyResolveTypeForMemberSelection(currMatchee.tok, currMatchee.Type).NormalizeExpand();
    if (currMatcheeType is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);
    }
    var dtd = currMatcheeType.AsDatatype;

    // Get all constructors of type matchee
    var subst = new Dictionary<TypeParameter, Type>();
    Dictionary<string, DatatypeCtor> ctors;
    if (dtd == null) {
      ctors = null;
    } else {

      ctors = dtd.Ctors.ToDictionary(c => c.Name, c => c);//resolver.datatypeCtors[dtd];
      Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage
      subst = Resolver.TypeSubstitutionMap(dtd.TypeArgs, currMatcheeType.TypeArgs); // Build the type-parameter substitution map for this use of the datatype
    }

    // Get the head of each patterns
    var patternHeads = branches.ConvertAll(new Converter<RBranch, ExtendedPattern>(GetPatternHead));
    var newBranches = branches.ConvertAll(new Converter<RBranch, RBranch>(DropPatternHead));
    var pairPB = patternHeads.Zip(newBranches, (x, y) => new Tuple<ExtendedPattern, RBranch>(x, y)).ToList();

    if (ctors != null && patternHeads.Exists(x => x is IdPattern && ((IdPattern)x).Arguments != null && ctors.ContainsKey(((IdPattern)x).Id))) {
      // ==[3]== If dtd is a datatype and at least one of the pattern is a constructor, create a match on currMatchee
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[3]=== Constructor Case");
      }

      return CompileRBranchConstructor(mti, context, currMatchee, subst, ctors, matchees, pairPB);
    } else if (dtd == null && patternHeads.Exists(x => (x is LitPattern || (x is IdPattern id && id.ResolvedLit != null)))) {
      // ==[3**]== If dtd is a base type and at least one of the pattern is a constant, create an If-then-else construct on the constant
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[3**]=== Constant Case");
      }

      return CompileRBranchConstant(mti, context, currMatchee, matchees, pairPB);
    } else {
      // ==[4]==  all head patterns are bound variables:
      if (mti.Debug) {
        Console.WriteLine("DEBUG: ===[4]=== Variable Case");
      }

      foreach (Tuple<ExtendedPattern, RBranch> PB in pairPB) {
        if (!(PB.Item1 is IdPattern)) {
          Contract.Assert(false); throw new cce.UnreachableException(); // in Variable case with a constant pattern
        }
        var currPattern = (IdPattern)PB.Item1;

        if (currPattern.Arguments != null) {
          if (dtd == null) {
            Contract.Assert(false); throw new cce.UnreachableException(); // non-nullary constructors of a non-datatype;
          } else {
            resolver.reporter.Error(MessageSource.Resolver, currPattern.Tok, "Type mismatch: expected constructor of type {0}.  Got {1}.", dtd.Name, currPattern.Id);
          }
        }
        // Optimization: Don't let-bind if name is a wildcard, either in source or generated
        LetBindNonWildCard(PB.Item2, currPattern, currMatchee);
      }
      if (mti.Debug) {
        Console.WriteLine("DEBUG: return");
      }
      return CompileRBranch(mti, context.AbstractHole(), matchees, pairPB.ToList().ConvertAll(new Converter<Tuple<ExtendedPattern, RBranch>, RBranch>(x => x.Item2)));
    }
  }
  
  /// <summary>
  /// A SyntaxContainer is a wrapper around either an Expression or a Statement
  /// It allows for generic functions over the two syntax spaces of Dafny
  /// </summary>
  private abstract class SyntaxContainer {
    public readonly IToken Tok;

    public SyntaxContainer(IToken tok) {
      this.Tok = tok;
    }
  }

  private class CExpr : SyntaxContainer {
    public readonly Expression Body;
    public Attributes Attributes;

    public CExpr(IToken tok, Expression body, Attributes attrs = null) : base(tok) {
      this.Body = body;
      this.Attributes = attrs;
    }
  }

  private class CStmt : SyntaxContainer {
    public readonly Statement Body;
    public Attributes Attributes;

    public CStmt(IToken tok, Statement body, Attributes attrs = null) : base(tok) {
      this.Body = body;
      this.Attributes = attrs;
    }
  }
  

  private SyntaxContainer PackBody(IToken tok, RBranch branch) {
    if (branch is RBranchStmt br) {
      return new CStmt(tok, new BlockStmt(tok, tok, br.Body), br.Attributes);
    } else if (branch is RBranchExpr) {
      return new CExpr(tok, ((RBranchExpr)branch).Body, ((RBranchExpr)branch).Attributes);
    } else {
      Contract.Assert(false); throw new cce.UnreachableException(); // RBranch has only two implementations
    }
  }

  private List<Statement> UnboxStmtContainer(SyntaxContainer con) {
    if (con is CStmt cstmt) {
      if (cstmt.Body is BlockStmt block) {
        return block.Body;
      } else {
        return new List<Statement>() { cstmt.Body };
      }
    } else {
      throw new NotImplementedException("Bug in CompileRBranch: expected a StmtContainer");
    }
  }
  
  /// Unwraps a CStmt and returns its Body as a BlockStmt
  private BlockStmt BlockStmtOfCStmt(IToken tok, IToken endTok, CStmt con) {
    var stmt = con.Body;
    if (stmt is BlockStmt) {
      return (BlockStmt)stmt;
    } else {
      var stmts = new List<Statement>();
      stmts.Add(stmt);
      return new BlockStmt(tok, endTok, stmts);
    }
  }
  
  /* Temporary information about the Match being desugared  */
  private class MatchTempInfo {
    public Type Type { get; }
    public IToken Tok;
    public IToken EndTok;
    public IToken[] BranchTok;
    public int[] BranchIDCount; // Records the number of copies of each branch
    public bool isStmt; // true if we are desugaring a MatchStmt, false if a MatchExpr
    public bool Debug;
    public readonly ResolutionContext CodeContext;
    public List<ExtendedPattern> MissingCases;
    public Attributes Attributes;

    public MatchTempInfo(Type type, IToken tok, int branchidnum, ResolutionContext codeContext, bool debug = false,
      Attributes attrs = null) {
      Type = type;
      int[] init = new int[branchidnum];
      for (int i = 0; i < branchidnum; i++) {
        init[i] = 1;
      }
      this.Tok = tok;
      this.EndTok = tok;
      this.BranchTok = new IToken[branchidnum];
      this.BranchIDCount = init;
      this.isStmt = false;
      this.Debug = debug;
      this.CodeContext = codeContext;
      this.MissingCases = new List<ExtendedPattern>();
      this.Attributes = attrs;
    }
    public MatchTempInfo(IToken tok, IToken endtok, int branchidnum, ResolutionContext codeContext, bool debug = false, Attributes attrs = null) {
      int[] init = new int[branchidnum];
      for (int i = 0; i < branchidnum; i++) {
        init[i] = 1;
      }
      this.Tok = tok;
      this.EndTok = endtok;
      this.BranchTok = new IToken[branchidnum];
      this.BranchIDCount = init;
      this.isStmt = true;
      this.Debug = debug;
      this.CodeContext = codeContext;
      this.MissingCases = new List<ExtendedPattern>();
      this.Attributes = attrs;
    }

    public void UpdateBranchID(int branchID, int update) {
      BranchIDCount[branchID] += update;
    }
  }
  
  /// <summary>
  /// RBranch is an intermediate data-structure representing a branch during pattern-match compilation
  /// </summary>
  private abstract class RBranch {
    public readonly IToken Tok;
    public int BranchID;
    public List<ExtendedPattern> Patterns;

    public RBranch(IToken tok, int branchid, List<ExtendedPattern> patterns) {
      Contract.Requires(patterns.All(p => !(p is DisjunctivePattern)));
      this.Tok = tok;
      this.BranchID = branchid;
      this.Patterns = patterns;
    }
  }


  private class RBranchStmt : RBranch {
    public List<Statement> Body;
    public Attributes Attributes;

    public RBranchStmt(IToken tok, int branchid, List<ExtendedPattern> patterns, List<Statement> body, Attributes attrs = null) : base(tok, branchid, patterns) {
      this.Body = body;
      this.Attributes = attrs;
    }

    public RBranchStmt(int branchid, NestedMatchCaseStmt x, Attributes attrs = null) : base(x.Tok, branchid, new List<ExtendedPattern>()) {
      Contract.Requires(!(x.Pat is DisjunctivePattern)); // No nested or patterns
      this.Body = new List<Statement>(x.Body); // Resolving the body will insert new elements.
      this.Attributes = attrs;
      this.Patterns.Add(x.Pat);
    }

    public override string ToString() {
      var bodyStr = "";
      foreach (var stmt in this.Body) {
        bodyStr += string.Format("{1}{0};\n", Printer.StatementToString(stmt), "\t");
      }
      return string.Format("\t> id: {0}\n\t> patterns: <{1}>\n\t-> body:\n{2} \n", this.BranchID, String.Join(",", this.Patterns.ConvertAll(x => x.ToString())), bodyStr);
    }
  }

  private class RBranchExpr : RBranch {

    public Expression Body;
    public Attributes Attributes;

    public RBranchExpr(IToken tok, int branchid, List<ExtendedPattern> patterns, Expression body, Attributes attrs = null) : base(tok, branchid, patterns) {
      this.Body = body;
      this.Attributes = attrs;
    }

    public RBranchExpr(int branchid, NestedMatchCaseExpr x, Attributes attrs = null) : base(x.Tok, branchid, new List<ExtendedPattern>()) {
      this.Body = x.Body;
      this.Patterns.Add(x.Pat);
      this.Attributes = attrs;
    }

    public override string ToString() {
      return string.Format("\t> id: {0}\n\t-> patterns: <{1}>\n\t-> body: {2}", this.BranchID, String.Join(",", this.Patterns.ConvertAll(x => x.ToString())), Printer.ExprToString(this.Body));
    }
  }


  // deep clone Patterns and Body
  private static RBranchStmt CloneRBranchStmt(RBranchStmt branch) {
    return new RBranchStmt(branch.Tok, branch.BranchID, branch.Patterns, branch.Body, branch.Attributes);
  }

  private static RBranchExpr CloneRBranchExpr(RBranchExpr branch) {
    return new RBranchExpr(branch.Tok, branch.BranchID, branch.Patterns, branch.Body, branch.Attributes);
  }

  private static RBranch CloneRBranch(RBranch branch) {
    if (branch is RBranchStmt) {
      return CloneRBranchStmt((RBranchStmt)branch);
    } else {
      return CloneRBranchExpr((RBranchExpr)branch);
    }
  }
  
  private static ExtendedPattern GetPatternHead(RBranch branch) {
    return branch.Patterns.First();
  }

  private static RBranch DropPatternHead(RBranch branch) {
    branch.Patterns.RemoveAt(0);
    return branch;
  }

  // let-bind a variable of name "name" and type "type" as "expr" on the body of "branch"
  private void LetBind(RBranch branch, IdPattern var, Expression genExpr) {
    var name = var.Id;
    var type = var.Type ?? new InferredTypeProxy();
    var isGhost = var.IsGhost;

    // if the expression is a generated IdentifierExpr, replace its token by the branch's
    Expression expr = genExpr;
    if (genExpr is IdentifierExpr idExpr) {
      if (idExpr.Name.StartsWith("_")) {
        expr = new IdentifierExpr(var.Tok, idExpr.Var);
      }
    }
    if (branch is RBranchStmt branchStmt) {
      if (branchStmt.Body.Count > 0) {
        var cLVar = new LocalVariable(var.Tok, var.Tok, name, type, isGhost);
        cLVar.type = type;
        var cPat = new CasePattern<LocalVariable>(cLVar.EndTok, cLVar);
        cPat.AssembleExpr(null); // TODO null?
        var cLet = new VarDeclPattern(cLVar.Tok, cLVar.Tok, cPat, expr, false);
        cLet.IsGhost = branchStmt.Body[0].IsGhost;
        
        var substituter = new Substituter(null, new Dictionary<IVariable, Expression>() {
          { var.BoundVar, new IdentifierExpr(var.BoundVar.tok, cLVar)}
        }, new Dictionary<TypeParameter, Type>());

        foreach (var stmt in branchStmt.Body) {
          ((INode) stmt).Visit(node => {
            ReflectiveUpdater.UpdateFieldsOfType<Expression>(node, expr => substituter.Substitute(expr));
            return true;
          });
        } 
        
        branchStmt.Body.Insert(0, cLet);
      }
    } else if (branch is RBranchExpr branchExpr) {
      var cBVar = var.BoundVar; //new BoundVar(var.Tok, name, type);
      cBVar.IsGhost = isGhost;
      var cPat = new CasePattern<BoundVar>(cBVar.Tok, cBVar);
      cPat.AssembleExpr(null); // TODO null?
      var cPats = new List<CasePattern<BoundVar>>();
      cPats.Add(cPat);
      var exprs = new List<Expression>();
      exprs.Add(expr);
      var cLet = new LetExpr(cBVar.tok, cPats, exprs, branchExpr.Body, true);
      cLet.Type = branchExpr.Body.Type;
      branchExpr.Body = cLet;
    }
  }

  // If cp is not a wildcard, replace branch.Body with let cp = expr in branch.Body
  // Otherwise do nothing
  private void LetBindNonWildCard(RBranch branch, IdPattern var, Expression expr) {
    if (!var.IsWildcardPattern) {
      LetBind(branch, var, expr);
    }
  }
}