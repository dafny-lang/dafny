//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public class ResolutionErrorReporter
  {
    public int ErrorCount = 0;

    /// <summary>
    /// This method is virtual, because it is overridden in the VSX plug-in for Dafny.
    /// </summary>
    public virtual void Error(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Red;
      Console.WriteLine("{0}({1},{2}): Error: {3}",
          DafnyOptions.Clo.UseBaseNameForFileName ? System.IO.Path.GetFileName(tok.filename) : tok.filename, tok.line, tok.col - 1,
          string.Format(msg, args));
      Console.ForegroundColor = col;
      ErrorCount++;
    }
    public void Error(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Error(d.tok, msg, args);
    }
    public void Error(Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Error(s.Tok, msg, args);
    }
    public void Error(NonglobalVariable v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Error(v.tok, msg, args);
    }
    public void Error(Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Error(e.tok, msg, args);
    }
    public void Warning(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Yellow;
      Console.WriteLine("{0}({1},{2}): Warning: {3}",
          DafnyOptions.Clo.UseBaseNameForFileName ? System.IO.Path.GetFileName(tok.filename) : tok.filename, tok.line, tok.col - 1,
          string.Format(msg, args));
      Console.ForegroundColor = col;
    }
  }

  public struct AdditionalInformation
  {
    public IToken Token;
    public string Text;
    public int Length;
  }

  public class Resolver : ResolutionErrorReporter
  {
    readonly BuiltIns builtIns;

    ModuleSignature moduleInfo = null;

    FreshIdGenerator defaultTempVarIdGenerator;
    string FreshTempVarName(string prefix, ICodeContext context)
    {
      var decl = context as Declaration;
      if (decl != null)
      {
        return decl.IdGenerator.FreshId(prefix);
      }
      // TODO(wuestholz): Is the following code ever needed?
      if (defaultTempVarIdGenerator == null)
      {
        defaultTempVarIdGenerator = new FreshIdGenerator();
      }
      return defaultTempVarIdGenerator.FreshId(prefix);
    }

    public Action<AdditionalInformation> AdditionalInformationReporter;

    internal void ReportAdditionalInformation(IToken token, string text, int length)
    {
      Contract.Requires(token != null);
      Contract.Requires(text != null);
      Contract.Requires(0 <= length);
      if (AdditionalInformationReporter != null) {
        AdditionalInformationReporter(new AdditionalInformation { Token = token, Text = text, Length = length });
      }
    }

    interface IAmbiguousThing<Thing>
    {
      /// <summary>
      /// Returns a non-zero number of non-null Thing's
      /// </summary>
      IEnumerable<Thing> AllDecls();
    }
    class AmbiguousTopLevelDecl : TopLevelDecl, IAmbiguousThing<TopLevelDecl>  // only used with "classes"
    {
      public override string WhatKind { get { return A.WhatKind; } }
      readonly TopLevelDecl A;
      readonly TopLevelDecl B;
      public AmbiguousTopLevelDecl(ModuleDefinition m, TopLevelDecl a, TopLevelDecl b)
        : base(a.tok, a.Name + "/" + b.Name, m, new List<TypeParameter>(), null) {
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        A = a;
        B = b;
      }
      public IEnumerable<TopLevelDecl> AllDecls() {
        foreach (var a in new TopLevelDecl[] { A, B }) {
          var amb = a as AmbiguousTopLevelDecl;
          if (amb != null) {
            foreach (var decl in amb.AllDecls()) {
              yield return decl;
            }
          } else {
            yield return a;
          }
        }
      }
      public string ModuleNames() {
        string nm;
        if (A is AmbiguousTopLevelDecl) {
          nm = ((AmbiguousTopLevelDecl)A).ModuleNames();
        } else {
          nm = A.Module.Name;
        }
        if (B is AmbiguousTopLevelDecl) {
          nm += ", " + ((AmbiguousTopLevelDecl)B).ModuleNames();
        } else {
          nm += ", " + B.Module.Name;
        }
        return nm;
      }
    }

    class AmbiguousMemberDecl : MemberDecl, IAmbiguousThing<MemberDecl>  // only used with "classes"
    {
      public override string WhatKind { get { return A.WhatKind; } }
      readonly MemberDecl A;
      readonly MemberDecl B;
      public AmbiguousMemberDecl(ModuleDefinition m, MemberDecl a, MemberDecl b)
        : base(a.tok, a.Name + "/" + b.Name, true, a.IsGhost, null) {
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        A = a;
        B = b;
      }
      public IEnumerable<MemberDecl> AllDecls() {
        var amb = A as AmbiguousMemberDecl;
        if (amb == null) {
          yield return A;
        } else {
          foreach (var decl in amb.AllDecls()) {
            yield return decl;
          }
        }
        amb = B as AmbiguousMemberDecl;
        if (amb == null) {
          yield return B;
        } else {
          foreach (var decl in amb.AllDecls()) {
            yield return decl;
          }
        }
      }
      public string ModuleNames() {
        string nm;
        if (A is AmbiguousMemberDecl) {
          nm = ((AmbiguousMemberDecl)A).ModuleNames();
        } else {
          nm = A.EnclosingClass.Module.Name;
        }
        if (B is AmbiguousMemberDecl) {
          nm += ", " + ((AmbiguousMemberDecl)B).ModuleNames();
        } else {
          nm += ", " + B.EnclosingClass.Module.Name;
        }
        return nm;
      }
    }
    //Dictionary<string, Tuple<DatatypeCtor, bool>> allDatatypeCtors;

    readonly Dictionary<ClassDecl, Dictionary<string, MemberDecl>> classMembers = new Dictionary<ClassDecl, Dictionary<string, MemberDecl>>();
    readonly Dictionary<DatatypeDecl, Dictionary<string, MemberDecl>> datatypeMembers = new Dictionary<DatatypeDecl, Dictionary<string, MemberDecl>>();
    readonly Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>> datatypeCtors = new Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>>();
    enum BasicTypeVariety { Bool = 0, Int, Real, None }  // note, these are ordered, so they can be used as indices into basicTypeMembers
    readonly Dictionary<string, MemberDecl>[] basicTypeMembers = new Dictionary<string, MemberDecl>[] {
      new Dictionary<string, MemberDecl>(),
      new Dictionary<string, MemberDecl>(),
      new Dictionary<string, MemberDecl>()
    };
    readonly Graph<ModuleDecl> dependencies = new Graph<ModuleDecl>();
    private ModuleSignature systemNameInfo = null;
    private bool useCompileSignatures = false;
    private RefinementTransformer refinementTransformer = null;

    public Resolver(Program prog) {
      Contract.Requires(prog != null);
      builtIns = prog.BuiltIns;
      // Populate the members of the basic types
      var trunc = new SpecialField(Token.NoToken, "Trunc", "ToBigInteger()", "", "", false, false, false, Type.Int, null);
      basicTypeMembers[(int)BasicTypeVariety.Real].Add(trunc.Name, trunc);
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(builtIns != null);
      Contract.Invariant(cce.NonNullElements(dependencies));
      Contract.Invariant(cce.NonNullDictionaryAndValues(classMembers) && Contract.ForAll(classMembers.Values, v => cce.NonNullDictionaryAndValues(v)));
      Contract.Invariant(cce.NonNullDictionaryAndValues(datatypeCtors) && Contract.ForAll(datatypeCtors.Values, v => cce.NonNullDictionaryAndValues(v)));
    }

    public void ResolveProgram(Program prog) {
      Contract.Requires(prog != null);
      var origErrorCount = ErrorCount;
      var bindings = new ModuleBindings(null);
      var b = BindModuleNames(prog.DefaultModuleDef, bindings);
      bindings.BindName("_module", prog.DefaultModule, b);
      if (ErrorCount > 0) { return; } // if there were errors, then the implict ModuleBindings data structure invariant
      // is violated, so Processing dependencies will not succeed.
      ProcessDependencies(prog.DefaultModule, b, dependencies);
      // check for cycles in the import graph
      List<ModuleDecl> cycle = dependencies.TryFindCycle();
      if (cycle != null) {
        var cy = Util.Comma(" -> ", cycle, m => m.Name);
        Error(cycle[0], "module definition contains a cycle (note: parent modules implicitly depend on submodules): {0}", cy);
      }
      if (ErrorCount > 0) { return; } // give up on trying to resolve anything else

      // fill in module heights
      List<ModuleDecl> sortedDecls = dependencies.TopologicallySortedComponents();
      int h = 0;
      foreach (ModuleDecl m in sortedDecls) {
        m.Height = h;
        if (m is LiteralModuleDecl) {
          var mdef = ((LiteralModuleDecl)m).ModuleDef;
          mdef.Height = h;
          prog.Modules.Add(mdef);
        }
        h++;
      }

      var rewriters = new List<IRewriter>();
      var refinementTransformer = new RefinementTransformer(this, AdditionalInformationReporter, prog);
      rewriters.Add(refinementTransformer);
      rewriters.Add(new AutoContractsRewriter());
      var opaqueRewriter = new OpaqueFunctionRewriter(this);
      rewriters.Add(new AutoReqFunctionRewriter(this, opaqueRewriter));
      rewriters.Add(opaqueRewriter);
      rewriters.Add(new TimeLimitRewriter());

      systemNameInfo = RegisterTopLevelDecls(prog.BuiltIns.SystemModule, false);
      prog.CompileModules.Add(prog.BuiltIns.SystemModule);
      foreach (var decl in sortedDecls) {
        if (decl is LiteralModuleDecl) {
          // The declaration is a literal module, so it has members and such that we need
          // to resolve. First we do refinement transformation. Then we construct the signature
          // of the module. This is the public, externally visible signature. Then we add in
          // everything that the system defines, as well as any "import" (i.e. "opened" modules)
          // directives (currently not supported, but this is where we would do it.) This signature,
          // which is only used while resolving the members of the module is stored in the (basically)
          // global variable moduleInfo. Then the signatures of the module members are resolved, followed
          // by the bodies.
          var literalDecl = (LiteralModuleDecl)decl;
          var m = literalDecl.ModuleDef;

          var errorCount = ErrorCount;
          foreach (var r in rewriters) {
            r.PreResolve(m);
          }

          literalDecl.Signature = RegisterTopLevelDecls(m, true);
          literalDecl.Signature.Refines = refinementTransformer.RefinedSig;
          var sig = literalDecl.Signature;
          // set up environment
          var preResolveErrorCount = ErrorCount;
          ResolveModuleDefinition(m, sig);
          foreach (var r in rewriters) {
            if (ErrorCount != preResolveErrorCount) {
              break;
            }
            r.PostResolve(m);
          }
          if (ErrorCount == errorCount && !m.IsAbstract) {
            // compilation should only proceed if everything is good, including the signature (which preResolveErrorCount does not include);
            Contract.Assert(!useCompileSignatures);
            useCompileSignatures = true;  // set Resolver-global flag to indicate that Signatures should be followed to their CompiledSignature
            var nw = new Cloner().CloneModuleDefinition(m, m.CompileName + "_Compile");
            var compileSig = RegisterTopLevelDecls(nw, true);
            compileSig.Refines = refinementTransformer.RefinedSig;
            sig.CompileSignature = compileSig;
            ResolveModuleDefinition(nw, compileSig);
            prog.CompileModules.Add(nw);
            useCompileSignatures = false;  // reset the flag
          }
        } else if (decl is AliasModuleDecl) {
          var alias = (AliasModuleDecl)decl;
          // resolve the path
          ModuleSignature p;
          if (ResolvePath(alias.Root, alias.Path, out p, this)) {
            alias.Signature = p;
          } else {
            alias.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else if (decl is ModuleFacadeDecl) {
          var abs = (ModuleFacadeDecl)decl;
          ModuleSignature p;
          if (ResolvePath(abs.Root, abs.Path, out p, this)) {
            abs.Signature = MakeAbstractSignature(p, abs.FullCompileName, abs.Height, prog.Modules);
            abs.OriginalSignature = p;
            ModuleSignature compileSig;
            if (abs.CompilePath != null) {
              if (ResolvePath(abs.CompileRoot, abs.CompilePath, out compileSig, this)) {
                if (refinementTransformer.CheckIsRefinement(compileSig, p)) {
                  abs.Signature.CompileSignature = compileSig;
                } else {
                  Error(abs.CompilePath[0],
                  "module " + Util.Comma(".", abs.CompilePath, x => x.val) + " must be a refinement of " + Util.Comma(".", abs.Path, x => x.val));
                }
                abs.Signature.IsGhost = compileSig.IsGhost;
                // always keep the ghost information, to supress a spurious error message when the compile module isn't actually a refinement
              }
            }
          } else {
            abs.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else { Contract.Assert(false); }
        Contract.Assert(decl.Signature != null);
      }
      if (ErrorCount != origErrorCount) {
        // do nothing else
        return;
      }
      // compute IsRecursive bit for mutually recursive functions and methods
      foreach (var module in prog.Modules) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          if (clbl is Function) {
            var fn = (Function)clbl;
            if (!fn.IsRecursive) {  // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(fn);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
                fn.IsRecursive = true;
              }
            }
            if (fn.IsRecursive && fn is CoPredicate) {
              // this means the corresponding prefix predicate is also recursive
              var prefixPred = ((CoPredicate)fn).PrefixPredicate;
              if (prefixPred != null) {
                prefixPred.IsRecursive = true;
              }
            }
          } else {
            var m = (Method)clbl;
            if (!m.IsRecursive) {  // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(m);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
                m.IsRecursive = true;
              }
            }
          }
        }
        foreach (var r in rewriters) {
          r.PostCyclicityResolve(module);
        }
      }
      // fill in default decreases clauses:  for functions and methods, and for loops
      FillInDefaultDecreasesClauses(prog);
      foreach (var module in prog.Modules) {
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is Method) {
            body = ((Method)clbl).Body;
          } else if (clbl is IteratorDecl) {
            body = ((IteratorDecl)clbl).Body;
          }
          if (body != null) {
            var c = new FillInDefaultLoopDecreases_Visitor(this, clbl);
            c.Visit(body);
          }
        }
      }
      foreach (var module in prog.Modules) {
        foreach (var iter in ModuleDefinition.AllIteratorDecls(module.TopLevelDecls)) {
          ReportAdditionalInformation(iter.tok, Printer.IteratorClassToString(iter), iter.Name.Length);
        }
      }
      // fill in other additional information
      foreach (var module in prog.Modules) {
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is Method) {
            body = ((Method)clbl).Body;
          } else if (clbl is IteratorDecl) {
            body = ((IteratorDecl)clbl).Body;
          }
          if (body != null) {
            var c = new ReportOtherAdditionalInformation_Visitor(this);
            c.Visit(body);
          }
        }
      }
    }

    void FillInDefaultDecreasesClauses(Program prog)
    {
      Contract.Requires(prog != null);

      foreach (var module in prog.Modules) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          ICallable m;
          string s;
          if (clbl is CoLemma) {
            var prefixLemma = ((CoLemma)clbl).PrefixLemma;
            m = prefixLemma;
            s = prefixLemma.Name + " ";
          } else {
            m = clbl;
            s = "";
          }
          var anyChangeToDecreases = FillInDefaultDecreases(m, true);

          if (anyChangeToDecreases || m.InferredDecreases || m is PrefixLemma) {
            bool showIt = false;
            if (m is Function) {
              // show the inferred decreases clause only if it will ever matter, i.e., if the function is recursive
              showIt = ((Function)m).IsRecursive;
            } else if (m is PrefixLemma) {
              // always show the decrease clause, since at the very least it will start with "_k", which the programmer did not write explicitly
              showIt = true;
            } else {
              showIt = ((Method)m).IsRecursive;
            }
            if (showIt) {
              s += "decreases ";
              if (m.Decreases.Expressions.Count != 0) {
                string sep = "";
                foreach (var d in m.Decreases.Expressions) {
                  s += sep + Printer.ExprToString(d);
                  sep = ", ";
                }
              }
              s += ";";  // always terminate with a semi-colon, even in the case of an empty decreases clause
              // Note, in the following line, we use the location information for "clbl", not "m".  These
              // are the same, except in the case where "clbl" is a CoLemma and "m" is a prefix lemma.
              ReportAdditionalInformation(clbl.Tok, s, clbl.Tok.val.Length);
            }
          }
        }
      }
    }

    /// <summary>
    /// Return "true" if this routine makes any change to the decreases clause.  If the decreases clause
    /// starts off essentially empty and a default is provided, then clbl.InferredDecreases is also set
    /// to true.
    /// </summary>
    bool FillInDefaultDecreases(ICallable clbl, bool addPrefixInCoClusters) {
      Contract.Requires(clbl != null);

      if (clbl is CoPredicate) {
        // copredicates don't have decreases clauses
        return false;
      }
      var anyChangeToDecreases = false;
      var decr = clbl.Decreases.Expressions;
      if (DafnyOptions.O.Dafnycc) {
        if (decr.Count > 1) {
          Error(decr[1].tok, "In dafnycc mode, only one decreases expression is allowed");
        }
        // In dafnycc mode, only consider first argument
        if (decr.Count == 0 && clbl.Ins.Count > 0) {
          var p = clbl.Ins[0];
          if (!(p is ImplicitFormal) && p.Type.IsOrdered) {
            var ie = new IdentifierExpr(p.tok, p.Name);
            ie.Var = p; ie.Type = p.Type;  // resolve it here
            decr.Add(ie);
            return true;
          }
        }
        return false;
      }
      if (decr.Count == 0 || (clbl is PrefixLemma && decr.Count == 1)) {
        // The default for a function starts with the function's reads clause, if any
        if (clbl is Function) {
          var fn = (Function)clbl;
          if (fn.Reads.Count != 0) {
            // start the default lexicographic tuple with the reads clause
            var r = FrameToObjectSet(fn.Reads);
            decr.Add(AutoGeneratedExpression.Create(r));
            anyChangeToDecreases = true;
          }
        }

        // Add one component for each parameter, unless the parameter's type is one that
        // doesn't appear useful to orderings.
        foreach (var p in clbl.Ins) {
          if (!(p is ImplicitFormal) && p.Type.IsOrdered) {
            var ie = new IdentifierExpr(p.tok, p.Name);
            ie.Var = p; ie.Type = p.Type;  // resolve it here
            decr.Add(AutoGeneratedExpression.Create(ie));
            anyChangeToDecreases = true;
          }
        }

        clbl.InferredDecreases = true;  // this indicates that finding a default decreases clause was attempted
      }
      if (addPrefixInCoClusters && clbl is Function) {
        var fn = (Function)clbl;
        switch (fn.CoClusterTarget) {
          case Function.CoCallClusterInvolvement.None:
            break;
          case Function.CoCallClusterInvolvement.IsMutuallyRecursiveTarget:
            // prefix: decreases 0,
            clbl.Decreases.Expressions.Insert(0, Expression.CreateIntLiteral(fn.tok, 0));
            anyChangeToDecreases = true;
            break;
          case Function.CoCallClusterInvolvement.CoRecursiveTargetAllTheWay:
            // prefix: decreases 1,
            clbl.Decreases.Expressions.Insert(0, Expression.CreateIntLiteral(fn.tok, 1));
            anyChangeToDecreases = true;
            break;
          default:
            Contract.Assume(false);  // unexpected case
            break;
        }
      }
      return anyChangeToDecreases;
    }

    public static Expression FrameArrowToObjectSet(Expression e, FreshIdGenerator idGen) {
      var arrTy = e.Type.AsArrowType;
      if (arrTy != null) {
        var bvars = new List<BoundVar>();
        var bexprs = new List<Expression>();
        foreach (var t in arrTy.Args) {
          var bv = new BoundVar(e.tok, idGen.FreshId("_x"), t);
          bvars.Add(bv);
          bexprs.Add(new IdentifierExpr(e.tok, bv.Name) { Type = bv.Type, Var = bv });
        }
        var oVar = new BoundVar(e.tok, idGen.FreshId("_o"), new ObjectType());
        var obj = new IdentifierExpr(e.tok, oVar.Name) { Type = oVar.Type, Var = oVar };
        bvars.Add(oVar);

        return
          new SetComprehension(e.tok, bvars,
            new BinaryExpr(e.tok, BinaryExpr.Opcode.In, obj,
              new ApplyExpr(e.tok, e, bexprs)
              {
                Type = new SetType(new ObjectType())
              })
            {
              ResolvedOp = BinaryExpr.ResolvedOpcode.InSet,
              Type = Type.Bool
            }, obj, null)
          {
            Type = new SetType(new ObjectType())
          };
      } else {
        return e;
      }
    }

    public static Expression FrameToObjectSet(List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      List<Expression> sets = new List<Expression>();
      List<Expression> singletons = null;
      var idGen = new FreshIdGenerator();
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        if (fe.E is WildcardExpr) {
          // drop wildcards altogether
        } else {
          Expression e = FrameArrowToObjectSet(fe.E, idGen);  // keep only fe.E, drop any fe.Field designation
          Contract.Assert(e.Type != null);  // should have been resolved already
          var eType = e.Type.NormalizeExpand();
          if (eType.IsRefType) {
            // e represents a singleton set
            if (singletons == null) {
              singletons = new List<Expression>();
            }
            singletons.Add(e);
          } else if (eType is SeqType) {
            // e represents a sequence
            // Add:  set x :: x in e
            var bv = new BoundVar(e.tok, idGen.FreshId("_s2s_"), ((SeqType)eType).Arg);
            var bvIE = new IdentifierExpr(e.tok, bv.Name);
            bvIE.Var = bv;  // resolve here
            bvIE.Type = bv.Type;  // resolve here
            var sInE = new BinaryExpr(e.tok, BinaryExpr.Opcode.In, bvIE, e);
            sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InSeq;  // resolve here
            sInE.Type = Type.Bool;  // resolve here
            var s = new SetComprehension(e.tok, new List<BoundVar>() { bv }, sInE, bvIE, null);
            s.Type = new SetType(new ObjectType());  // resolve here
            sets.Add(s);
          } else {
            // e is already a set
            Contract.Assert(eType is SetType);
            sets.Add(e);
          }
        }
      }
      if (singletons != null) {
        Expression display = new SetDisplayExpr(singletons[0].tok, singletons);
        display.Type = new SetType(new ObjectType());  // resolve here
        sets.Add(display);
      }
      if (sets.Count == 0) {
        Expression emptyset = new SetDisplayExpr(Token.NoToken, new List<Expression>());
        emptyset.Type = new SetType(new ObjectType());  // resolve here
        return emptyset;
      } else {
        Expression s = sets[0];
        for (int i = 1; i < sets.Count; i++) {
          BinaryExpr union = new BinaryExpr(s.tok, BinaryExpr.Opcode.Add, s, sets[i]);
          union.ResolvedOp = BinaryExpr.ResolvedOpcode.Union;  // resolve here
          union.Type = new SetType(new ObjectType());  // resolve here
          s = union;
        }
        return s;
      }
    }

    private void ResolveModuleDefinition(ModuleDefinition m, ModuleSignature sig) {
      moduleInfo = MergeSignature(sig, systemNameInfo);
      // resolve
      var datatypeDependencies = new Graph<IndDatatypeDecl>();
      var codatatypeDependencies = new Graph<CoDatatypeDecl>();
      int prevErrorCount = ErrorCount;
      ResolveAttributes(m.Attributes, new ResolveOpts(new NoContext(m.Module), false));
      ResolveTopLevelDecls_Signatures(m, m.TopLevelDecls, datatypeDependencies, codatatypeDependencies);
      if (ErrorCount == prevErrorCount) {
        ResolveTopLevelDecls_Meat(m.TopLevelDecls, datatypeDependencies, codatatypeDependencies);
      }
    }


    public class ModuleBindings
    {
      private ModuleBindings parent;
      private Dictionary<string, ModuleDecl> modules;
      private Dictionary<string, ModuleBindings> bindings;

      public ModuleBindings(ModuleBindings p) {
        parent = p;
        modules = new Dictionary<string, ModuleDecl>();
        bindings = new Dictionary<string, ModuleBindings>();
      }
      public bool BindName(string name, ModuleDecl subModule, ModuleBindings b) {
        if (modules.ContainsKey(name)) {
          return false;
        } else {
          modules.Add(name, subModule);
          bindings.Add(name, b);
          return true;
        }
      }
      public bool TryLookup(IToken name, out ModuleDecl m) {
        Contract.Requires(name != null);
        if (modules.TryGetValue(name.val, out m)) {
          return true;
        } else if (parent != null) {
          return parent.TryLookup(name, out m);
        } else return false;
      }
      public bool TryLookupIgnore(IToken name, out ModuleDecl m, ModuleDecl ignore) {
        Contract.Requires(name != null);
        if (modules.TryGetValue(name.val, out m) && m != ignore) {
          return true;
        } else if (parent != null) {
          return parent.TryLookup(name, out m);
        } else return false;
      }
      public IEnumerable<ModuleDecl> ModuleList {
        get { return modules.Values; }
      }
      public ModuleBindings SubBindings(string name) {
        ModuleBindings v = null;
        bindings.TryGetValue(name, out v);
        return v;
      }
    }
    private ModuleBindings BindModuleNames(ModuleDefinition moduleDecl, ModuleBindings parentBindings) {
      var bindings = new ModuleBindings(parentBindings);

      foreach (var tld in moduleDecl.TopLevelDecls) {
        if (tld is LiteralModuleDecl) {
          var subdecl = (LiteralModuleDecl)tld;
          var subBindings = BindModuleNames(subdecl.ModuleDef, bindings);
          if (!bindings.BindName(subdecl.Name, subdecl, subBindings)) {
            Error(subdecl.tok, "Duplicate module name: {0}", subdecl.Name);
          }
        } else if (tld is ModuleFacadeDecl) {
          var subdecl = (ModuleFacadeDecl)tld;
          if (!bindings.BindName(subdecl.Name, subdecl, null)) {
            Error(subdecl.tok, "Duplicate module name: {0}", subdecl.Name);
          }
        } else if (tld is AliasModuleDecl) {
          var subdecl = (AliasModuleDecl)tld;
          if (!bindings.BindName(subdecl.Name, subdecl, null)) {
            Error(subdecl.tok, "Duplicate module name: {0}", subdecl.Name);
          }
        }
      }
      return bindings;
    }

    private void ProcessDependenciesDefinition(ModuleDecl decl, ModuleDefinition m, ModuleBindings bindings, Graph<ModuleDecl> dependencies) {
      if (m.RefinementBaseName != null) {
        ModuleDecl other;
        if (!bindings.TryLookup(m.RefinementBaseName[0], out other)) {
          Error(m.RefinementBaseName[0], "module {0} named as refinement base does not exist", m.RefinementBaseName[0].val);
        } else if (other is LiteralModuleDecl && ((LiteralModuleDecl)other).ModuleDef == m) {
          Error(m.RefinementBaseName[0], "module cannot refine itself: {0}", m.RefinementBaseName[0].val);
        } else {
          Contract.Assert(other != null);  // follows from postcondition of TryGetValue
          dependencies.AddEdge(decl, other);
          m.RefinementBaseRoot = other;
        }
      }
      foreach (var toplevel in m.TopLevelDecls) {
        if (toplevel is ModuleDecl) {
          var d = (ModuleDecl)toplevel;
          dependencies.AddEdge(decl, d);
          var subbindings = bindings.SubBindings(d.Name);
          ProcessDependencies(d, subbindings ?? bindings, dependencies);
        }
      }
    }
    private void ProcessDependencies(ModuleDecl moduleDecl, ModuleBindings bindings, Graph<ModuleDecl> dependencies) {
      dependencies.AddVertex(moduleDecl);
      if (moduleDecl is LiteralModuleDecl) {
        ProcessDependenciesDefinition(moduleDecl, ((LiteralModuleDecl)moduleDecl).ModuleDef, bindings, dependencies);
      } else if (moduleDecl is AliasModuleDecl) {
        var alias = moduleDecl as AliasModuleDecl;
        ModuleDecl root;
        if (!bindings.TryLookupIgnore(alias.Path[0], out root, alias))
          Error(alias.tok, ModuleNotFoundErrorMessage(0, alias.Path));
        else {
          dependencies.AddEdge(moduleDecl, root);
          alias.Root = root;
        }
      } else if (moduleDecl is ModuleFacadeDecl) {
        var abs = moduleDecl as ModuleFacadeDecl;
        ModuleDecl root;
        if (!bindings.TryLookup(abs.Path[0], out root))
          Error(abs.tok, ModuleNotFoundErrorMessage(0, abs.Path));
        else {
          dependencies.AddEdge(moduleDecl, root);
          abs.Root = root;
        }
        if (abs.CompilePath != null) {
          if (!bindings.TryLookup(abs.CompilePath[0], out root))
            Error(abs.tok, ModuleNotFoundErrorMessage(0, abs.CompilePath));
          else {
            dependencies.AddEdge(moduleDecl, root);
            abs.CompileRoot = root;
          }
        }
      }
    }

    private static string ModuleNotFoundErrorMessage(int i, List<IToken> path) {
      Contract.Requires(path != null);
      Contract.Requires(0 <= i && i < path.Count);
      return "module " + path[i].val + " does not exist" +
        (1 < path.Count ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.val) + ")" : "");
    }

    public static ModuleSignature MergeSignature(ModuleSignature m, ModuleSignature system) {
      var info = new ModuleSignature();
      // add the system-declared information, among which we know there are no duplicates
      foreach (var kv in system.TopLevels) {
        info.TopLevels.Add(kv.Key, kv.Value);
      }
      foreach (var kv in system.Ctors) {
        info.Ctors.Add(kv.Key, kv.Value);
      }
      // add for the module itself
      foreach (var kv in m.TopLevels) {
        info.TopLevels[kv.Key] = kv.Value;
      }
      foreach (var kv in m.Ctors) {
        info.Ctors[kv.Key] = kv.Value;
      }
      foreach (var kv in m.StaticMembers) {
        info.StaticMembers[kv.Key] = kv.Value;
      }
      info.IsGhost = m.IsGhost;
      return info;
    }
    ModuleSignature RegisterTopLevelDecls(ModuleDefinition moduleDef, bool useImports) {
      Contract.Requires(moduleDef != null);
      var sig = new ModuleSignature();
      sig.ModuleDef = moduleDef;
      sig.IsGhost = moduleDef.IsAbstract;
      List<TopLevelDecl> declarations = moduleDef.TopLevelDecls;

      if (useImports) {
        // First go through and add anything from the opened imports
        foreach (var im in declarations) {
          if (im is ModuleDecl && ((ModuleDecl)im).Opened) {
            var s = GetSignature(((ModuleDecl)im).Signature);
            // classes:
            foreach (var kv in s.TopLevels) {
              TopLevelDecl d;
              if (sig.TopLevels.TryGetValue(kv.Key, out d)) {
                sig.TopLevels[kv.Key] = new AmbiguousTopLevelDecl(moduleDef, d, kv.Value);
              } else {
                sig.TopLevels.Add(kv.Key, kv.Value);
              }
            }
            // constructors:
            foreach (var kv in s.Ctors) {
              Tuple<DatatypeCtor, bool> pair;
              if (sig.Ctors.TryGetValue(kv.Key, out pair)) {
                // mark it as a duplicate
                sig.Ctors[kv.Key] = new Tuple<DatatypeCtor, bool>(pair.Item1, true);
              } else {
                // add new
                sig.Ctors.Add(kv.Key, kv.Value);
              }
            }
            // static members:
            foreach (var kv in s.StaticMembers) {
              MemberDecl md;
              if (sig.StaticMembers.TryGetValue(kv.Key, out md)) {
                sig.StaticMembers[kv.Key] = new AmbiguousMemberDecl(moduleDef, md, kv.Value);
              } else {
                // add new
                sig.StaticMembers.Add(kv.Key, kv.Value);
              }
            }
          }
        }
      }
      // This is solely used to detect duplicates amongst the various e
      Dictionary<string, TopLevelDecl> toplevels = new Dictionary<string, TopLevelDecl>();
      // Now add the things present
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        // register the class/datatype/module name
        if (toplevels.ContainsKey(d.Name)) {
          Error(d, "Duplicate name of top-level declaration: {0}", d.Name);
        } else {
          toplevels[d.Name] = d;
          sig.TopLevels[d.Name] = d;
        }
        if (d is ModuleDecl) {
          // nothing to do
        } else if (d is OpaqueTypeDecl) {
          // nothing more to register
        } else if (d is TypeSynonymDecl) {
          // nothing more to register
        } else if (d is NewtypeDecl) {
          // nothing more to register

        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;

          // register the names of the implicit members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(iter, members);

          // First, register the iterator's in- and out-parameters as readonly fields
          foreach (var p in iter.Ins) {
            if (members.ContainsKey(p.Name)) {
              Error(p, "Name of in-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              var field = new SpecialField(p.tok, p.Name, p.CompileName, "", "", p.IsGhost, false, false, p.Type, null);
              field.EnclosingClass = iter;  // resolve here
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }
          foreach (var p in iter.Outs) {
            if (members.ContainsKey(p.Name)) {
              Error(p, "Name of yield-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              var field = new SpecialField(p.tok, p.Name, p.CompileName, "", "", p.IsGhost, true, true, p.Type, null);
              field.EnclosingClass = iter;  // resolve here
              iter.OutsFields.Add(field);
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }
          foreach (var p in iter.Outs) {
            var nm = p.Name + "s";
            if (members.ContainsKey(nm)) {
              Error(p.tok, "Name of implicit yield-history variable '{0}' is already used by another member of the iterator", p.Name);
            } else {
              var tp = new SeqType(p.Type.IsSubrangeType ? new IntType() : p.Type);
              var field = new SpecialField(p.tok, nm, nm, "", "", true, true, false, tp, null);
              field.EnclosingClass = iter;  // resolve here
              iter.OutsHistoryFields.Add(field);  // for now, just record this field (until all parameters have been added as members)
            }
          }
          // now that already-used 'ys' names have been checked for, add these yield-history variables
          iter.OutsHistoryFields.ForEach(f => {
            members.Add(f.Name, f);
            iter.Members.Add(f);
          });
          // add the additional special variables as fields
          iter.Member_Reads = new SpecialField(iter.tok, "_reads", "_reads",          "", "", true, false, false, new SetType(new ObjectType()), null);
          iter.Member_Modifies = new SpecialField(iter.tok, "_modifies", "_modifies", "", "", true, false, false, new SetType(new ObjectType()), null);
          iter.Member_New = new SpecialField(iter.tok, "_new", "_new",                "", "", true, true, true, new SetType(new ObjectType()), null);
          foreach (var field in new List<Field>() { iter.Member_Reads, iter.Member_Modifies, iter.Member_New }) {
            field.EnclosingClass = iter;  // resolve here
            members.Add(field.Name, field);
            iter.Members.Add(field);
          }
          // finally, add special variables to hold the components of the (explicit or implicit) decreases clause
          FillInDefaultDecreases(iter, false);
          // create the fields; unfortunately, we don't know their types yet, so we'll just insert type proxies for now
          var i = 0;
          foreach (var p in iter.Decreases.Expressions) {
            var nm = "_decreases" + i;
            var field = new SpecialField(p.tok, nm, nm, "", "", true, false, false, new InferredTypeProxy(), null);
            field.EnclosingClass = iter;  // resolve here
            iter.DecreasesFields.Add(field);
            members.Add(field.Name, field);
            iter.Members.Add(field);
            i++;
          }

          // Note, the typeArgs parameter to the following Method/Predicate constructors is passed in as the empty list.  What that is
          // saying is that the Method/Predicate does not take any type parameters over and beyond what the enclosing type (namely, the
          // iterator type) does.
          // --- here comes the constructor
          var init = new Constructor(iter.tok, "_ctor", new List<TypeParameter>(), iter.Ins,
            new List<MaybeFreeExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<MaybeFreeExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // --- here comes predicate Valid()
          var valid = new Predicate(iter.tok, "Valid", false, true, true, new List<TypeParameter>(),
            new List<Formal>(),
            new List<Expression>(),
            new List<FrameExpression>(),
            new List<Expression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, Predicate.BodyOriginKind.OriginalOrInherited, null, null);
          // --- here comes method MoveNext
          var moveNext = new Method(iter.tok, "MoveNext", false, false, new List<TypeParameter>(),
            new List<Formal>(), new List<Formal>() { new Formal(iter.tok, "more", Type.Bool, false, false) },
            new List<MaybeFreeExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<MaybeFreeExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // add these implicit members to the class
          init.EnclosingClass = iter;
          valid.EnclosingClass = iter;
          moveNext.EnclosingClass = iter;
          iter.HasConstructor = true;
          iter.Member_Init = init;
          iter.Member_Valid = valid;
          iter.Member_MoveNext = moveNext;
          MemberDecl member;
          if (members.TryGetValue(init.Name, out member)) {
            Error(member.tok, "member name '{0}' is already predefined for this iterator", init.Name);
          } else {
            members.Add(init.Name, init);
            iter.Members.Add(init);
          }
          // If the name of the iterator is "Valid" or "MoveNext", one of the following will produce an error message.  That
          // error message may not be as clear as it could be, but the situation also seems unlikely to ever occur in practice.
          if (members.TryGetValue("Valid", out member)) {
            Error(member.tok, "member name 'Valid' is already predefined for iterators");
          } else {
            members.Add(valid.Name, valid);
            iter.Members.Add(valid);
          }
          if (members.TryGetValue("MoveNext", out member)) {
            Error(member.tok, "member name 'MoveNext' is already predefined for iterators");
          } else {
            members.Add(moveNext.Name, moveNext);
            iter.Members.Add(moveNext);
          }

        } else if (d is ClassDecl) {
          ClassDecl cl = (ClassDecl)d;

          // register the names of the class members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(cl, members);

          bool hasConstructor = false;
          foreach (MemberDecl m in cl.Members) {
            if (!members.ContainsKey(m.Name)) {
              members.Add(m.Name, m);
              if (m is CoPredicate || m is CoLemma) {
                var extraName = m.Name + "#";
                MemberDecl extraMember;
                var cloner = new Cloner();
                var formals = new List<Formal>();
                var k = new ImplicitFormal(m.tok, "_k", new NatType(), true, false);
                formals.Add(k);
                if (m is CoPredicate) {
                  var cop = (CoPredicate)m;
                  formals.AddRange(cop.Formals.ConvertAll(cloner.CloneFormal));

                  List<TypeParameter> tyvars = cop.TypeArgs.ConvertAll(cloner.CloneTypeParam);

                  // create prefix predicate
                  cop.PrefixPredicate = new PrefixPredicate(cop.tok, extraName, cop.HasStaticKeyword, cop.IsProtected,
                    tyvars, k, formals,
                    cop.Req.ConvertAll(cloner.CloneExpr),
                    cop.Reads.ConvertAll(cloner.CloneFrameExpr),
                    cop.Ens.ConvertAll(cloner.CloneExpr),
                    new Specification<Expression>(new List<Expression>() { new IdentifierExpr(cop.tok, k.Name) }, null),
                    cop.Body,
                    null,
                    cop);
                  extraMember = cop.PrefixPredicate;
                  // In the call graph, add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
                  moduleDef.CallGraph.AddEdge(cop.PrefixPredicate, cop);
                } else {
                  var com = (CoLemma)m;
                  // _k has already been added to 'formals', so append the original formals
                  formals.AddRange(com.Ins.ConvertAll(cloner.CloneFormal));
                  // prepend _k to the given decreases clause
                  var decr = new List<Expression>();
                  decr.Add(new IdentifierExpr(com.tok, k.Name));
                  decr.AddRange(com.Decreases.Expressions.ConvertAll(cloner.CloneExpr));
                  // Create prefix lemma.  Note that the body is not cloned, but simply shared.
                  com.PrefixLemma = new PrefixLemma(com.tok, extraName, com.HasStaticKeyword,
                    com.TypeArgs.ConvertAll(cloner.CloneTypeParam), k, formals, com.Outs.ConvertAll(cloner.CloneFormal),
                    com.Req.ConvertAll(cloner.CloneMayBeFreeExpr), cloner.CloneSpecFrameExpr(com.Mod),
                    new List<MaybeFreeExpression>(),  // Note, the postconditions are filled in after the colemma's postconditions have been resolved
                    new Specification<Expression>(decr, null),
                    null, // Note, the body for the prefix method will be created once the call graph has been computed and the SCC for the colemma is known
                    cloner.CloneAttributes(com.Attributes), com);
                  extraMember = com.PrefixLemma;
                  // In the call graph, add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
                  moduleDef.CallGraph.AddEdge(com.PrefixLemma, com);
                }
                members.Add(extraName, extraMember);
              }
            } else if (m is Constructor && !((Constructor)m).HasName) {
              Error(m, "More than one anonymous constructor");
            } else {
              Error(m, "Duplicate member name: {0}", m.Name);
            }
            if (m is Constructor) {
              hasConstructor = true;
            }
          }
          cl.HasConstructor = hasConstructor;
          if (cl is TraitDecl && cl.HasConstructor)
          {
              Error(cl, "a trait is not allowed to declare a constructor");
          }
          if (cl.IsDefaultClass) {
            foreach (MemberDecl m in cl.Members) {
              Contract.Assert(!m.HasStaticKeyword || DafnyOptions.O.AllowGlobals);  // note, the IsStatic value isn't available yet; when it becomes available, we expect it will have the value 'true'
              if (m is Function || m is Method) {
                sig.StaticMembers[m.Name] = m;
              }
            }
          }

        } else {
          DatatypeDecl dt = (DatatypeDecl)d;

          // register the names of the constructors
          var ctors = new Dictionary<string, DatatypeCtor>();
          datatypeCtors.Add(dt, ctors);
          // ... and of the other members
          var members = new Dictionary<string, MemberDecl>();
          datatypeMembers.Add(dt, members);

          foreach (DatatypeCtor ctor in dt.Ctors) {
            if (ctor.Name.EndsWith("?")) {
              Error(ctor, "a datatype constructor name is not allowed to end with '?'");
            } else if (ctors.ContainsKey(ctor.Name)) {
              Error(ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
            } else {
              ctors.Add(ctor.Name, ctor);

              // create and add the query "method" (field, really)
              string queryName = ctor.Name + "?";
              var query = new SpecialField(ctor.tok, queryName, "is_" + ctor.CompileName, "", "", false, false, false, Type.Bool, null);
              query.EnclosingClass = dt;  // resolve here
              members.Add(queryName, query);
              ctor.QueryField = query;

              // also register the constructor name globally
              Tuple<DatatypeCtor, bool> pair;
              if (sig.Ctors.TryGetValue(ctor.Name, out pair)) {
                // mark it as a duplicate
                sig.Ctors[ctor.Name] = new Tuple<DatatypeCtor, bool>(pair.Item1, true);
              } else {
                // add new
                sig.Ctors.Add(ctor.Name, new Tuple<DatatypeCtor, bool>(ctor, false));
              }
            }
          }
          // add deconstructors now (that is, after the query methods have been added)
          foreach (DatatypeCtor ctor in dt.Ctors) {
            foreach (var formal in ctor.Formals) {
              bool nameError = false;
              if (formal.HasName && members.ContainsKey(formal.Name)) {
                Error(ctor, "Name of deconstructor is used by another member of the datatype: {0}", formal.Name);
                nameError = true;
              }
              var dtor = new DatatypeDestructor(formal.tok, ctor, formal, formal.Name, "dtor_" + formal.CompileName, "", "", formal.IsGhost, formal.Type, null);
              dtor.EnclosingClass = dt;  // resolve here
              if (!nameError && formal.HasName) {
                members.Add(formal.Name, dtor);
              }
              ctor.Destructors.Add(dtor);
            }
          }
        }
      }
      return sig;
    }

    private ModuleSignature MakeAbstractSignature(ModuleSignature p, string Name, int Height, List<ModuleDefinition> mods) {
      var mod = new ModuleDefinition(Token.NoToken, Name + ".Abs", true, true, null, null, null, false);
      mod.Height = Height;
      foreach (var kv in p.TopLevels) {
        mod.TopLevelDecls.Add(CloneDeclaration(kv.Value, mod, mods, Name));
      }
      var sig = RegisterTopLevelDecls(mod, false);
      sig.Refines = p.Refines;
      sig.CompileSignature = p;
      sig.IsGhost = p.IsGhost;
      mods.Add(mod);
      ResolveModuleDefinition(mod, sig);
      return sig;
    }

    TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m, List<ModuleDefinition> mods, string Name) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is ModuleFacadeDecl) {
        var abs = (ModuleFacadeDecl)d;
        var sig = MakeAbstractSignature(abs.OriginalSignature, Name + "." + abs.Name, abs.Height, mods);
        var a = new ModuleFacadeDecl(abs.Path, abs.tok, m, abs.CompilePath, abs.Opened);
        a.Signature = sig;
        a.OriginalSignature = abs.OriginalSignature;
        return a;
      } else {
        return new ClonerButDropMethodBodies().CloneDeclaration(d, m);
      }
    }


    public static bool ResolvePath(ModuleDecl root, List<IToken> Path, out ModuleSignature p, ResolutionErrorReporter reporter) {
      Contract.Requires(reporter != null);
      p = root.Signature;
      int i = 1;
      while (i < Path.Count) {
        ModuleSignature pp;
        if (p.FindSubmodule(Path[i].val, out pp)) {
          p = pp;
          i++;
        } else {
          reporter.Error(Path[i], ModuleNotFoundErrorMessage(i, Path));
          break;
        }
      }
      return i == Path.Count;
    }
    public void ResolveTopLevelDecls_Signatures(ModuleDefinition def, List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(datatypeDependencies != null);
      Contract.Requires(codatatypeDependencies != null);

      var typeRedirectionDependencies = new Graph<RedirectingTypeDecl>();
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        if (d is OpaqueTypeDecl) {
          // nothing to do
        } else if (d is TypeSynonymDecl) {
          var syn = (TypeSynonymDecl)d;
          ResolveType(syn.tok, syn.Rhs, syn, ResolveTypeOptionEnum.AllowPrefix, syn.TypeArgs);
          syn.Rhs.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null) {
              typeRedirectionDependencies.AddEdge(syn, s);
            }
          });
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveType(dd.tok, dd.BaseType, dd, ResolveTypeOptionEnum.DontInfer, null);
          dd.BaseType.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
        } else if (d is IteratorDecl) {
          ResolveIteratorSignature((IteratorDecl)d);
        } else if (d is ClassDecl) {
          ResolveClassMemberTypes((ClassDecl)d);
        } else if (d is ModuleDecl) {
          var decl = (ModuleDecl)d;
          if (!def.IsAbstract) {
            if (decl.Signature.IsGhost)
              {
                if (!(def.IsDefaultModule)) // _module is allowed to contain abstract modules, but not be abstract itself. Note this presents a challenge to
                                            // trusted verification, as toplevels can't be trusted if they invoke abstract module members.
                Error(d.tok, "an abstract module can only be imported into other abstract modules, not a concrete one.");
              } else {
                // physical modules are allowed everywhere
              }
          } else {
            // everything is allowed in an abstract module
          }
        } else {
          ResolveCtorTypes((DatatypeDecl)d, datatypeDependencies, codatatypeDependencies);
        }
        allTypeParameters.PopMarker();
      }

      // Now that all traits have been resolved, let classes inherit the trait members
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          InheritTraitMembers(cl);
        }
      }

      // perform acyclicity test on type synonyms
      var cycle = typeRedirectionDependencies.TryFindCycle();
      if (cycle != null) {
        Contract.Assert(cycle.Count != 0);
        var erste = cycle[0];
        Error(erste.Tok, "Cycle among redirecting types (newtypes, type synonyms): {0} -> {1}", Util.Comma(" -> ", cycle, syn => syn.Name), erste.Name);
      }
    }

    private readonly List<SetComprehension> needFiniteBoundsChecks_SetComprehension = new List<SetComprehension>();
    private readonly List<LetExpr> needFiniteBoundsChecks_LetSuchThatExpr = new List<LetExpr>();
    public int NFBC_Count {
      // provided just for the purpose of conveniently writing contracts for ResolveTopLevelDecl_Meat
      get {
        return needFiniteBoundsChecks_SetComprehension.Count + needFiniteBoundsChecks_LetSuchThatExpr.Count;
      }
    }

    static readonly List<NativeType> NativeTypes = new List<NativeType>() {
      new NativeType("byte", 0, 0x100, "", true),
      new NativeType("sbyte", -0x80, 0x80, "", true),
      new NativeType("ushort", 0, 0x10000, "", true),
      new NativeType("short", -0x8000, 0x8000, "", true),
      new NativeType("uint", 0, 0x100000000, "U", false),
      new NativeType("int", -0x80000000, 0x80000000, "", false),
      new NativeType("ulong", 0, new BigInteger(0x100000000) * new BigInteger(0x100000000), "UL", false),
      new NativeType("long", Int64.MinValue, 0x8000000000000000, "L", false),
    };

    public void ResolveTopLevelDecls_Meat(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies));
      Contract.Requires(cce.NonNullElements(codatatypeDependencies));
      Contract.Requires(NFBC_Count == 0);
      Contract.Ensures(NFBC_Count == 0);

      int prevErrorCount = ErrorCount;

      // Resolve the meat of classes and iterators, the definitions of type synonyms, and the type parameters of all top-level type declarations
      // First, resolve the newtype declarations and the constraint clauses, including filling in .ResolvedOp fields.  This is needed for the
      // resolution of the other declarations, because those other declarations may invoke DiscoverBounds, which looks at the .Constraint field
      // of any newtypes involved.  DiscoverBounds is called on quantifiers (but only in non-ghost contexts) and set comprehensions (in all
      // contexts).  The constraints of newtypes are ghost, so DiscoverBounds is not going to be called on any quantifiers they may contain.
      // However, the constraints may contain set comprehensions.  For this reason, we postpone the DiscoverBounds checks on set comprehensions.
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveAttributes(d.Attributes, new ResolveOpts(new NoContext(d.Module), false));
          // this check can be done only after it has been determined that the redirected types do not involve cycles
          if (!dd.BaseType.IsNumericBased()) {
            Error(dd.tok, "newtypes must be based on some numeric type (got {0})", dd.BaseType);
          }
          // type check the constraint, if any
          if (dd.Var != null) {
            Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.BaseType));  // follows from NewtypeDecl invariant
            Contract.Assert(dd.Constraint != null);  // follows from NewtypeDecl invariant
            scope.PushMarker();
            var added = scope.Push(dd.Var.Name, dd.Var);
            Contract.Assert(added);
            ResolveType(dd.Var.tok, dd.Var.Type, dd, ResolveTypeOptionEnum.DontInfer, null);
            ResolveExpression(dd.Constraint, new ResolveOpts(dd, false, true));
            Contract.Assert(dd.Constraint.Type != null);  // follows from postcondition of ResolveExpression
            if (!UnifyTypes(dd.Constraint.Type, Type.Bool)) {
              Error(dd.Constraint, "newtype constraint must be of type bool (instead got {0})", dd.Constraint.Type);
            }
            if (!CheckTypeInference_Visitor.IsDetermined(dd.BaseType.NormalizeExpand())) {
              Error(dd.tok, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
            CheckTypeInference(dd.Constraint);
            scope.PopMarker();
          }
        }
      }
      // Now, we're ready for the other declarations.
      foreach (TopLevelDecl d in declarations) {
        if (d is TraitDecl && d.TypeArgs.Count > 0)
        {
            Error(d, "a trait cannot declare type parameters");
        }
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        if (!(d is IteratorDecl)) {
          // Note, attributes of iterators are resolved by ResolvedIterator, after registering any names in the iterator signature
          ResolveAttributes(d.Attributes, new ResolveOpts(new NoContext(d.Module), false));
        }
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          ResolveIterator(iter);
          ResolveClassMemberBodies(iter);  // resolve the automatically generated members
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          ResolveClassMemberBodies(cl);
        }
        allTypeParameters.PopMarker();
      }

      if (ErrorCount == prevErrorCount) {
        foreach (var e in needFiniteBoundsChecks_SetComprehension) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.Range);  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            e.MissingBounds = missingBounds;
            foreach (var bv in e.MissingBounds) {
              Error(e, "a set comprehension must produce a finite set, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
            }
          }
        }
        foreach (var e in needFiniteBoundsChecks_LetSuchThatExpr) {
          Contract.Assert(!e.Exact);  // only let-such-that expressions are ever added to the list
          Contract.Assert(e.RHSs.Count == 1);  // if we got this far, the resolver will have checked this condition successfully
          var constraint = e.RHSs[0];
          var missingBounds = new List<IVariable>();
          CheckTypeInference(constraint);  // we need to resolve operators before the call to DiscoverBounds
          var allBounds = DiscoverBoundsAux(e.tok, new List<IVariable>(e.BoundVars), constraint, true, true, true, missingBounds);
          if (missingBounds.Count != 0) {
            e.Constraint_MissingBounds = missingBounds;
            foreach (var bv in e.Constraint_MissingBounds) {
              Error(e, "a non-ghost let-such-that constraint must be compilable, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
            }
          } else {
            e.Constraint_Bounds = new List<ComprehensionExpr.BoundedPool>();
            foreach (var pair in allBounds) {
              Contract.Assert(1 <= pair.Item2.Count);
              // TODO: The following could be improved by picking the bound that is most likely to give rise to an efficient compiled program
              e.Constraint_Bounds.Add(pair.Item2[0]);
            }
          }
        }
      }
      needFiniteBoundsChecks_SetComprehension.Clear();
      needFiniteBoundsChecks_LetSuchThatExpr.Clear();

      Dictionary<string, NativeType> nativeTypeMap = new Dictionary<string, NativeType>();
      foreach (var nativeType in NativeTypes) {
        nativeTypeMap.Add(nativeType.Name, nativeType);
      }

      if (ErrorCount == prevErrorCount) {
        // Check that type inference went well everywhere; this will also fill in the .ResolvedOp field in binary expressions
        foreach (TopLevelDecl d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            iter.Members.Iter(CheckTypeInference_Member);
            if (iter.Body != null) {
              CheckTypeInference(iter.Body);
            }
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            cl.Members.Iter(CheckTypeInference_Member);
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            bool? boolNativeType = null;
            NativeType stringNativeType = null;
            object nativeTypeAttr = true;
            bool hasNativeTypeAttr = Attributes.ContainsMatchingValue(dd.Attributes, "nativeType", ref nativeTypeAttr,
              new Attributes.MatchingValueOption[] {
                Attributes.MatchingValueOption.Empty,
                Attributes.MatchingValueOption.Bool,
                Attributes.MatchingValueOption.String },
              err => Error(dd, err));
            if (hasNativeTypeAttr) {
              if (nativeTypeAttr is bool) {
                boolNativeType = (bool)nativeTypeAttr;
              } else {
                string keyString = (string)nativeTypeAttr;
                if (nativeTypeMap.ContainsKey(keyString)) {
                  stringNativeType = nativeTypeMap[keyString];
                } else {
                  Error(dd, "Unsupported nativeType {0}", keyString);
                }
              }
            }
            if (stringNativeType != null || boolNativeType == true) {
              if (!dd.BaseType.IsNumericBased(Type.NumericPersuation.Int)) {
                Error(dd, "nativeType can only be used on integral types");
              }
              if (dd.Var == null) {
                Error(dd, "nativeType can only be used if newtype specifies a constraint");
              }
            }
            if (dd.Var != null) {
              Contract.Assert(dd.Constraint != null);
              CheckTypeInference(dd.Constraint);

              Func<Expression, BigInteger?> GetConst = null;
              GetConst = (Expression e) => {
                int m = 1;
                BinaryExpr bin = e as BinaryExpr;
                if (bin != null && bin.Op == BinaryExpr.Opcode.Sub && GetConst(bin.E0) == BigInteger.Zero) {
                  m = -1;
                  e = bin.E1;
                }
                LiteralExpr l = e as LiteralExpr;
                if (l != null && l.Value is BigInteger) {
                  return m * (BigInteger)l.Value;
                }
                return null;
              };
              var missingBounds = new List<BoundVar>();
              var bounds = DiscoverBounds(dd.Constraint.tok, new List<BoundVar> { dd.Var }, dd.Constraint,
                true, true, missingBounds);
              List<NativeType> potentialNativeTypes =
                (stringNativeType != null) ? new List<NativeType> { stringNativeType } :
                (boolNativeType == false) ? new List<NativeType>() :
                NativeTypes;
              foreach (var nt in potentialNativeTypes) {
                if (missingBounds.Count == 0) {
                  bool lowerOk = false;
                  bool upperOk = false;
                  foreach (var bound in bounds) {
                    if (bound is ComprehensionExpr.IntBoundedPool) {
                      var bnd = (ComprehensionExpr.IntBoundedPool)bound;
                      if (bnd.LowerBound != null) {
                        BigInteger? lower = GetConst(bnd.LowerBound);
                        if (lower != null && nt.LowerBound <= lower) {
                          lowerOk = true;
                        }
                      }
                      if (bnd.UpperBound != null) {
                        BigInteger? upper = GetConst(bnd.UpperBound);
                        if (upper != null && upper <= nt.UpperBound) {
                          upperOk = true;
                        }
                      }
                    }
                  }
                  if (lowerOk && upperOk) {
                    dd.NativeType = nt;
                    break;
                  }
                }
              }
              if (dd.NativeType == null && (boolNativeType == true || stringNativeType != null)) {
                Error(dd, "Dafny's heuristics cannot find a compatible native type.  " +
                  "Hint: try writing a newtype constraint of the form 'i:int | lowerBound <= i < upperBound && (...any additional constraints...)'");
              }
              if (dd.NativeType != null && stringNativeType == null) {
                ReportAdditionalInformation(dd.tok, "{:nativeType \"" + dd.NativeType.Name + "\"}", dd.tok.val.Length);
              }
            }
          }
        }
      }

      if (ErrorCount == prevErrorCount) {
        // fill in the postconditions and bodies of prefix lemmas
        foreach (var com in ModuleDefinition.AllCoLemmas(declarations)) {
          var prefixLemma = com.PrefixLemma;
          if (prefixLemma == null) {
            continue;  // something went wrong during registration of the prefix lemma (probably a duplicated colemma name)
          }
          Contract.Assume(prefixLemma.Ens.Count == 0 && prefixLemma.Body == null);  // these are not supposed to have been filled in before
          // compute the postconditions of the prefix lemma
          var k = prefixLemma.Ins[0];
          foreach (var p in com.Ens) {
            var coConclusions = new HashSet<Expression>();
            CheckCoLemmaConclusions(p.E, true, coConclusions);
            var subst = new CoLemmaPostconditionSubstituter(coConclusions, new IdentifierExpr(k.tok, k.Name), this);
            var post = subst.CloneExpr(p.E);
            prefixLemma.Ens.Add(new MaybeFreeExpression(post, p.IsFree));
          }
          // Compute the statement body of the prefix lemma
          if (com.Body != null) {
            var kMinusOne = new BinaryExpr(com.tok, BinaryExpr.Opcode.Sub, new IdentifierExpr(k.tok, k.Name), new LiteralExpr(com.tok, 1));
            var subst = new CoLemmaBodyCloner(com, kMinusOne, this);
            var mainBody = subst.CloneBlockStmt(com.Body);
            var kPositive = new BinaryExpr(com.tok, BinaryExpr.Opcode.Lt, new LiteralExpr(com.tok, 0), new IdentifierExpr(k.tok, k.Name));
            var condBody = new IfStmt(com.BodyStartTok, mainBody.EndTok, kPositive, mainBody, null);
            prefixLemma.Body = new BlockStmt(com.tok, condBody.EndTok, new List<Statement>() { condBody });
          }
          // The prefix lemma now has all its components, so it's finally time we resolve it
          currentClass = (ClassDecl)prefixLemma.EnclosingClass;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(currentClass.TypeArgs, false, currentClass);
          ResolveTypeParameters(prefixLemma.TypeArgs, false, prefixLemma);
          ResolveMethod(prefixLemma);
          allTypeParameters.PopMarker();
          currentClass = null;
          CheckTypeInference_Member(prefixLemma);
        }
      }

      // Perform the stratosphere check on inductive datatypes, and compute to what extent the inductive datatypes require equality support
      foreach (var dtd in datatypeDependencies.TopologicallySortedComponents()) {
        if (datatypeDependencies.GetSCCRepresentative(dtd) == dtd) {
          // do the following check once per SCC, so call it on each SCC representative
          SccStratosphereCheck(dtd, datatypeDependencies);
          DetermineEqualitySupport(dtd, datatypeDependencies);
        }
      }

      // Set the SccRepr field of codatatypes
      foreach (var repr in codatatypeDependencies.TopologicallySortedComponents()) {
        foreach (var codt in codatatypeDependencies.GetSCC(repr)) {
          codt.SscRepr = repr;
        }
      }

      if (ErrorCount == prevErrorCount) {  // because CheckCoCalls requires the given expression to have been successfully resolved
        // Perform the guardedness check on co-datatypes
        foreach (var repr in ModuleDefinition.AllFunctionSCCs(declarations)) {
          var module = repr.EnclosingModule;
          bool dealsWithCodatatypes = false;
          foreach (var m in module.CallGraph.GetSCC(repr)) {
            var f = m as Function;
            if (f != null && f.ResultType.InvolvesCoDatatype) {
              dealsWithCodatatypes = true;
              break;
            }
          }
          var coCandidates = new List<CoCallResolution.CoCallInfo>();
          var hasIntraClusterCallsInDestructiveContexts = false;
          foreach (var m in module.CallGraph.GetSCC(repr)) {
            var f = m as Function;
            if (f != null && f.Body != null) {
              var checker = new CoCallResolution(f, dealsWithCodatatypes);
              checker.CheckCoCalls(f.Body);
              coCandidates.AddRange(checker.FinalCandidates);
              hasIntraClusterCallsInDestructiveContexts |= checker.HasIntraClusterCallsInDestructiveContexts;
            } else if (f == null) {
              // the SCC contains a method, which we always consider to be a destructive context
              hasIntraClusterCallsInDestructiveContexts = true;
            }
          }
          if (coCandidates.Count != 0) {
            if (hasIntraClusterCallsInDestructiveContexts) {
              foreach (var c in coCandidates) {
                c.CandidateCall.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsInDestructiveContext;
              }
            } else {
              foreach (var c in coCandidates) {
                c.CandidateCall.CoCall = FunctionCallExpr.CoCallResolution.Yes;
                c.EnclosingCoConstructor.IsCoCall = true;
                ReportAdditionalInformation(c.CandidateCall.tok, "co-recursive call", c.CandidateCall.Name.Length);
              }
              // Finally, fill in the CoClusterTarget field
              // Start by setting all the CoClusterTarget fields to CoRecursiveTargetAllTheWay.
              foreach (var m in module.CallGraph.GetSCC(repr)) {
                var f = (Function)m;  // the cast is justified on account of that we allow co-recursive calls only in clusters that have no methods at all
                f.CoClusterTarget = Function.CoCallClusterInvolvement.CoRecursiveTargetAllTheWay;
              }
              // Then change the field to IsMutuallyRecursiveTarget whenever we see a non-self recursive non-co-recursive call
              foreach (var m in module.CallGraph.GetSCC(repr)) {
                var f = (Function)m;  // cast is justified just like above
                foreach (var call in f.AllCalls) {
                  if (call.CoCall != FunctionCallExpr.CoCallResolution.Yes && call.Function != f && ModuleDefinition.InSameSCC(f, call.Function)) {
                    call.Function.CoClusterTarget = Function.CoCallClusterInvolvement.IsMutuallyRecursiveTarget;
                  }
                }
              }
            }
          }
        }
        // Inferred required equality support for datatypes and for Function and Method signatures
        // First, do datatypes until a fixpoint is reached
        bool inferredSomething;
        do {
          inferredSomething = false;
          foreach (var d in declarations) {
            if (d is DatatypeDecl) {
              var dt = (DatatypeDecl)d;
              foreach (var tp in dt.TypeArgs) {
                if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                  // here's our chance to infer the need for equality support
                  foreach (var ctor in dt.Ctors) {
                    foreach (var arg in ctor.Formals) {
                      if (InferRequiredEqualitySupport(tp, arg.Type)) {
                        tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                        inferredSomething = true;
                        goto DONE_DT;  // break out of the doubly-nested loop
                      }
                    }
                  }
                DONE_DT: ;
                }
              }
            }
          }
        } while (inferredSomething);
        // Now do it for Function and Method signatures
        foreach (var d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            var done = false;
            foreach (var tp in iter.TypeArgs) {
              if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                foreach (var p in iter.Ins) {
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    done = true;
                    break;
                  }
                }
                foreach (var p in iter.Outs) {
                  if (done) break;
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    break;
                  }
                }
              }
            }
          } else  if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              if (!member.IsGhost) {
                if (member is Function) {
                  var f = (Function)member;
                  foreach (var tp in f.TypeArgs) {
                    if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                      // here's our chance to infer the need for equality support
                      if (InferRequiredEqualitySupport(tp, f.ResultType)) {
                        tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                      } else {
                        foreach (var p in f.Formals) {
                          if (InferRequiredEqualitySupport(tp, p.Type)) {
                            tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                            break;
                          }
                        }
                      }
                    }
                  }
                } else if (member is Method) {
                  var m = (Method)member;
                  bool done = false;
                  foreach (var tp in m.TypeArgs) {
                    if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                      // here's our chance to infer the need for equality support
                      foreach (var p in m.Ins) {
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          done = true;
                          break;
                        }
                      }
                      foreach (var p in m.Outs) {
                        if (done) break;
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          break;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        // Check that all == and != operators in non-ghost contexts are applied to equality-supporting types.
        // Note that this check can only be done after determining which expressions are ghosts.
        foreach (var d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            foreach (var p in iter.Ins) {
              if (!p.IsGhost) {
                CheckEqualityTypes_Type(p.tok, p.Type);
              }
            }
            foreach (var p in iter.Outs) {
              if (!p.IsGhost) {
                CheckEqualityTypes_Type(p.tok, p.Type);
              }
            }
            if (iter.Body != null) {
              CheckEqualityTypes_Stmt(iter.Body);
            }
          } else  if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              if (!member.IsGhost) {
                if (member is Field) {
                  var f = (Field)member;
                  CheckEqualityTypes_Type(f.tok, f.Type);
                } else if (member is Function) {
                  var f = (Function)member;
                  foreach (var p in f.Formals) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  CheckEqualityTypes_Type(f.tok, f.ResultType);
                  if (f.Body != null) {
                    CheckEqualityTypes(f.Body);
                  }
                } else if (member is Method) {
                  var m = (Method)member;
                  foreach (var p in m.Ins) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  foreach (var p in m.Outs) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  if (m.Body != null) {
                    CheckEqualityTypes_Stmt(m.Body);
                  }
                }
              }
            }
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var p in ctor.Formals) {
                if (!p.IsGhost) {
                  CheckEqualityTypes_Type(p.tok, p.Type);
                }
              }
            }
          }
        }
        // Check that copredicates are not recursive with non-copredicate functions, and
        // check that colemmas are not recursive with non-colemma methods.
        // Also, check that newtypes sit in their own SSC.
        foreach (var d in declarations) {
          if (d is ClassDecl) {
            foreach (var member in ((ClassDecl)d).Members) {
              if (member is CoPredicate) {
                var fn = (CoPredicate)member;
                // Check here for the presence of any 'ensures' clauses, which are not allowed (because we're not sure
                // of their soundness)
                if (fn.Ens.Count != 0) {
                  Error(fn.Ens[0].tok, "a copredicate is not allowed to declare any ensures clause");
                }
                // Also check for 'reads' clauses
                if (fn.Reads.Count != 0) {
                  Error(fn.Reads[0].tok, "a copredicate is not allowed to declare any reads clause");  // (why?)
                }
                if (fn.Body != null) {
                  CoPredicateChecks(fn.Body, fn, CallingPosition.Positive);
                }
              } else if (member is CoLemma) {
                var m = (CoLemma)member;
                if (m.Body != null) {
                  CoLemmaChecks(m.Body, m);
                }
              }
            }
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            if (dd.Module.CallGraph.GetSCCSize(dd) != 1) {
              var cycle = Util.Comma(" -> ", dd.Module.CallGraph.GetSCC(dd), clbl => clbl.NameRelativeToModule);
              Error(dd.tok, "recursive dependency involving a newtype: " + cycle);
            }
          }
        }
      }
    }

    // ------------------------------------------------------------------------------------------------------
    // ----- Visitors ---------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region Visitors
    class ResolverBottomUpVisitor : BottomUpVisitor
    {
      protected Resolver resolver;
      public ResolverBottomUpVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
      public void Error(IToken tok, string msg, params object[] args) {
        Contract.Requires(tok != null);
        Contract.Requires(msg != null);
        Contract.Requires(args != null);
        resolver.Error(tok, msg, args);
      }
      public void Error(Expression expr, string msg, params object[] args) {
        Contract.Requires(expr != null);
        Contract.Requires(msg != null);
        Contract.Requires(args != null);
        Error(expr.tok, msg, args);
      }
    }
    abstract class ResolverTopDownVisitor<T> : TopDownVisitor<T>
    {
      Resolver resolver;
      public ResolverTopDownVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
      protected void Error(IToken tok, string msg, params object[] args)
      {
        Contract.Requires(tok != null);
        Contract.Requires(msg != null);
        Contract.Requires(args != null);
        resolver.Error(tok, msg, args);
      }
      protected void Error(Expression expr, string msg, params object[] args)
      {
        Contract.Requires(expr != null);
        Contract.Requires(msg != null);
        Contract.Requires(args != null);
        Error(expr.tok, msg, args);
      }
      protected void ReportAdditionalInformation(IToken tok, string text, int length)
      {
        Contract.Requires(tok != null);
        resolver.ReportAdditionalInformation(tok, text, length);
      }
    }
    #endregion Visitors

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckTypeInference -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CheckTypeInference
    private void CheckTypeInference_Member(MemberDecl member) {
      if (member is Method) {
        var m = (Method)member;
        m.Req.Iter(CheckTypeInference_MaybeFreeExpression);
        m.Ens.Iter(CheckTypeInference_MaybeFreeExpression);
        CheckTypeInference_Specification_FrameExpr(m.Mod);
        CheckTypeInference_Specification_Expr(m.Decreases);
        if (m.Body != null) {
          CheckTypeInference(m.Body);
          bool tail = true;
          bool hasTailRecursionPreference = Attributes.ContainsBool(m.Attributes, "tailrecursion", ref tail);
          if (hasTailRecursionPreference && !tail) {
            // the user specifically requested no tail recursion, so do nothing else
          } else if (hasTailRecursionPreference && tail && m.IsGhost) {
            Error(m.tok, "tail recursion can be specified only for methods that will be compiled, not for ghost methods");
          } else {
            var module = m.EnclosingClass.Module;
            var sccSize = module.CallGraph.GetSCCSize(m);
            if (hasTailRecursionPreference && 2 <= sccSize) {
              Error(m.tok, "sorry, tail-call optimizations are not supported for mutually recursive methods");
            } else if (hasTailRecursionPreference || sccSize == 1) {
              CallStmt tailCall = null;
              var status = CheckTailRecursive(m.Body.Body, m, ref tailCall, hasTailRecursionPreference);
              if (status != TailRecursionStatus.NotTailRecursive) {
                m.IsTailRecursive = true;
                if (tailCall != null) {
                  // this means there was at least one recursive call
                  ReportAdditionalInformation(m.tok, "tail recursive", m.Name.Length);
                }
              }
            }
          }
        }
      } else if (member is Function) {
        var f = (Function)member;
        var errorCount = ErrorCount;
        f.Req.Iter(CheckTypeInference);
        f.Ens.Iter(CheckTypeInference);
        f.Reads.Iter(fe => CheckTypeInference(fe.E));
        CheckTypeInference_Specification_Expr(f.Decreases);
        if (f.Body != null) {
          CheckTypeInference(f.Body);
          bool tail = true;
          if (Attributes.ContainsBool(f.Attributes, "tailrecursion", ref tail) && tail) {
            Error(f.tok, "sorry, tail-call functions are not supported");
          }
        }
        if (errorCount == ErrorCount && f is CoPredicate) {
          var cop = (CoPredicate)f;
          CheckTypeInference_Member(cop.PrefixPredicate);
        }
      }
    }
    private void CheckTypeInference_MaybeFreeExpression(MaybeFreeExpression mfe) {
      Contract.Requires(mfe != null);
      foreach (var e in Attributes.SubExpressions(mfe.Attributes)) {
        CheckTypeInference(e);
      }
      CheckTypeInference(mfe.E);
    }
    private void CheckTypeInference_Specification_Expr(Specification<Expression> spec) {
      Contract.Requires(spec != null);
      foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
        CheckTypeInference(e);
      }
      spec.Expressions.Iter(CheckTypeInference);
    }
    private void CheckTypeInference_Specification_FrameExpr(Specification<FrameExpression> spec) {
      Contract.Requires(spec != null);
      foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
        CheckTypeInference(e);
      }
      spec.Expressions.Iter(fe => CheckTypeInference(fe.E));
    }
    void CheckTypeInference(Expression expr) {
      Contract.Requires(expr != null);
      var c = new CheckTypeInference_Visitor(this);
      c.Visit(expr);
    }
    void CheckTypeInference(Statement stmt) {
      Contract.Requires(stmt != null);
      var c = new CheckTypeInference_Visitor(this);
      c.Visit(stmt);
    }
    class CheckTypeInference_Visitor : ResolverBottomUpVisitor
    {
      public CheckTypeInference_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          foreach (var local in s.Locals) {
            CheckTypeIsDetermined(local.Tok, local.Type, "local variable");
          }
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          s.BoundVars.Iter(bv => CheckTypeIsDetermined(bv.tok, bv.Type, "bound variable"));
        }
      }
      protected override void VisitOneExpr(Expression expr) {
        if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          if (e != null) {
            foreach (var bv in e.BoundVars) {
              if (!IsDetermined(bv.Type.Normalize())) {
                Error(bv.tok, "type of bound variable '{0}' could not be determined; please specify the type explicitly",
                  bv.Name);
              }
            }
          }
        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          if (e.Member is Function || e.Member is Method) {
            foreach (var p in e.TypeApplication) {
              if (!IsDetermined(p.Normalize())) {
                Error(e.tok, "type '{0}' to the {2} '{1}' is not determined", p, e.Member.Name, e.Member.WhatKind);
              }
            }
          }
        } else if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          foreach (var p in e.TypeArgumentSubstitutions) {
            if (!IsDetermined(p.Value.Normalize())) {
              Error(e.tok, "type variable '{0}' in the function call to '{1}' could not be determined{2}", p.Key.Name, e.Name,
                (e.Name.Contains("reveal_") || e.Name.Contains("_FULL"))
                ? ". If you are making an opaque function, make sure that the function can be called."
                : ""
              );
            }
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var p in e.LHSs) {
            foreach (var x in p.Vars) {
              if (!IsDetermined(x.Type.Normalize())) {
                Error(e.tok, "the type of the bound variable '{0}' could not be determined", x.Name);
              }
            }
          }
        } else if (expr is IdentifierExpr) {
          // by specializing for IdentifierExpr, error messages will be clearer
          CheckTypeIsDetermined(expr.tok, expr.Type, "variable");
        } else if (CheckTypeIsDetermined(expr.tok, expr.Type, "expression")) {
          var bin = expr as BinaryExpr;
          if (bin != null) {
            bin.ResolvedOp = ResolveOp(bin.Op, bin.E1.Type);
          }
        }
      }
      /// <summary>
      /// This method checks to see if 't' has been determined and returns the result.
      /// However, if t denotes an int-based or real-based type, then t is set to int or real,
      /// respectively, here.  Similarly, if t is an unresolved type for "null", then t
      /// is set to "object".
      /// </summary>
      public static bool IsDetermined(Type t) {
        Contract.Requires(t != null);
        Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
        // If the type specifies an arbitrary int-based or real-based type, just fill it in with int or real, respectively
        if (t is OperationTypeProxy) {
          var proxy = (OperationTypeProxy)t;
          if (proxy.JustInts) {
            proxy.T = Type.Int;
            return true;
          } else if (proxy.JustReals) {
            proxy.T = Type.Real;
            return true;
          }
        } else if (t is ObjectTypeProxy) {
          var proxy = (ObjectTypeProxy)t;
          proxy.T = new ObjectType();
          return true;
        }
        return !(t is TypeProxy);  // all other proxies indicate the type has not yet been determined
      }
      ISet<TypeProxy> UnderspecifiedTypeProxies = new HashSet<TypeProxy>();
      bool CheckTypeIsDetermined(IToken tok, Type t, string what) {
        Contract.Requires(tok != null);
        Contract.Requires(t != null);
        Contract.Requires(what != null);
        t = t.NormalizeExpand();
        // If the type specifies an arbitrary int-based or real-based type, just fill it in with int or real, respectively;
        // similarly, if t refers to the type of "null", set its type to be "object".
        if (t is OperationTypeProxy) {
          var proxy = (OperationTypeProxy)t;
          if (proxy.JustInts) {
            proxy.T = Type.Int;
            return true;
          } else if (proxy.JustReals) {
            proxy.T = Type.Real;
            return true;
          }
        } else if (t is ObjectTypeProxy) {
          var proxy = (ObjectTypeProxy)t;
          proxy.T = new ObjectType();
          return true;
        }

        if (t is TypeProxy) {
          var proxy = (TypeProxy)t;
          if (!UnderspecifiedTypeProxies.Contains(proxy)) {
            // report an error for this TypeProxy only once
            Error(tok, "the type of this {0} is underspecified", what);
            UnderspecifiedTypeProxies.Add(proxy);
          }
          return false;
        }
        // Recurse on type arguments:
        if (t is MapType) {
          return CheckTypeIsDetermined(tok, ((MapType)t).Range, what) &&
                 CheckTypeIsDetermined(tok, ((MapType)t).Domain, what);
        } else if (t is CollectionType) {
          return CheckTypeIsDetermined(tok, ((CollectionType)t).Arg, what);
        } else if (t is UserDefinedType) {
          return t.TypeArgs.All(rg => CheckTypeIsDetermined(tok, rg, what));
        } else {
          return true;
        }
      }
    }
    #endregion CheckTypeInference

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckTailRecursive -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CheckTailRecursive
    enum TailRecursionStatus
    {
      NotTailRecursive, // contains code that makes the enclosing method body not tail recursive (in way that is supported)
      CanBeFollowedByAnything, // the code just analyzed does not do any recursive calls
      TailCallSpent, // the method body is tail recursive, provided that all code that follows it in the method body is ghost
    }

    /// <summary>
    /// Checks if "stmts" can be considered tail recursive, and (provided "reportsError" is true) reports an error if not.
    /// Note, the current implementation is rather conservative in its analysis; upon need, the
    /// algorithm could be improved.
    /// In the current implementation, "enclosingMethod" is not allowed to be a mutually recursive method.
    ///
    /// The incoming value of "tailCall" is not used, but it's nevertheless a 'ref' parameter to allow the
    /// body to return the incoming value or to omit assignments to it.
    /// If the return value is CanBeFollowedByAnything, "tailCall" is unchanged.
    /// If the return value is TailCallSpent, "tailCall" shows one of the calls where the tail call was spent.  (Note,
    /// there could be several if the statements have branches.)
    /// If the return value is NoTailRecursive, "tailCall" could be anything.  In this case, an error
    /// message has been reported (provided "reportsErrors" is true).
    /// </summary>
    TailRecursionStatus CheckTailRecursive(List<Statement> stmts, Method enclosingMethod, ref CallStmt tailCall, bool reportErrors) {
      Contract.Requires(stmts != null);
      var status = TailRecursionStatus.CanBeFollowedByAnything;
      foreach (var s in stmts) {
        if (!s.IsGhost) {
          if (s is ReturnStmt && ((ReturnStmt)s).hiddenUpdate == null) {
            return status;
          }
          if (status == TailRecursionStatus.TailCallSpent) {
            // a tail call cannot be followed by non-ghost code
            if (reportErrors) {
              Error(tailCall.Tok, "this recursive call is not recognized as being tail recursive, because it is followed by non-ghost code");
            }
            return TailRecursionStatus.NotTailRecursive;
          }
          status = CheckTailRecursive(s, enclosingMethod, ref tailCall, reportErrors);
          if (status == TailRecursionStatus.NotTailRecursive) {
            return status;
          }
        }
      }
      return status;
    }

    /// <summary>
    /// See CheckTailRecursive(List Statement, ...), including its description of "tailCall".
    /// In the current implementation, "enclosingMethod" is not allowed to be a mutually recursive method.
    /// </summary>
    TailRecursionStatus CheckTailRecursive(Statement stmt, Method enclosingMethod, ref CallStmt tailCall, bool reportErrors) {
      Contract.Requires(stmt != null);
      if (stmt.IsGhost) {
        return TailRecursionStatus.NotTailRecursive;
      }
      if (stmt is PrintStmt) {
      } else if (stmt is BreakStmt) {
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        if (s.hiddenUpdate != null) {
          return CheckTailRecursive(s.hiddenUpdate, enclosingMethod, ref tailCall, reportErrors);
        }
      } else if (stmt is AssignStmt) {
      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        if (s.Body != null) {
          return CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        if (s.Method == enclosingMethod) {
          // It's a recursive call.  It can be considered a tail call only if the LHS of the call are the
          // formal out-parameters of the method
          for (int i = 0; i < s.Lhs.Count; i++) {
            var formal = enclosingMethod.Outs[i];
            if (!formal.IsGhost) {
              var lhs = s.Lhs[i] as IdentifierExpr;
              if (lhs != null && lhs.Var == formal) {
                // all is good
              } else {
                if (reportErrors) {
                  Error(s.Tok, "the recursive call to '{0}' is not tail recursive because the actual out-parameter {1} is not the formal out-parameter '{2}'", s.Method.Name, i, formal.Name);
                }
                return TailRecursionStatus.NotTailRecursive;
              }
            }
          }
          tailCall = s;
          return TailRecursionStatus.TailCallSpent;
        }
      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        return CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        var stThen = CheckTailRecursive(s.Thn, enclosingMethod, ref tailCall, reportErrors);
        if (stThen == TailRecursionStatus.NotTailRecursive) {
          return stThen;
        }
        var stElse = s.Els == null ? TailRecursionStatus.CanBeFollowedByAnything : CheckTailRecursive(s.Els, enclosingMethod, ref tailCall, reportErrors);
        if (stElse == TailRecursionStatus.NotTailRecursive) {
          return stElse;
        } else if (stThen == TailRecursionStatus.TailCallSpent || stElse == TailRecursionStatus.TailCallSpent) {
          return TailRecursionStatus.TailCallSpent;
        }
      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        var status = TailRecursionStatus.CanBeFollowedByAnything;
        foreach (var alt in s.Alternatives) {
          var st = CheckTailRecursive(alt.Body, enclosingMethod, ref tailCall, reportErrors);
          if (st == TailRecursionStatus.NotTailRecursive) {
            return st;
          } else if (st == TailRecursionStatus.TailCallSpent) {
            status = st;
          }
        }
        return status;
      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        var status = TailRecursionStatus.NotTailRecursive;
        if (s.Body != null) {
          status = CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
        if (status != TailRecursionStatus.CanBeFollowedByAnything) {
          if (status == TailRecursionStatus.NotTailRecursive) {
            // an error has already been reported
          } else if (reportErrors) {
            Error(tailCall.Tok, "a recursive call inside a loop is not recognized as being a tail call");
          }
          return TailRecursionStatus.NotTailRecursive;
        }
      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          var status = CheckTailRecursive(alt.Body, enclosingMethod, ref tailCall, reportErrors);
          if (status != TailRecursionStatus.CanBeFollowedByAnything) {
            if (status == TailRecursionStatus.NotTailRecursive) {
              // an error has already been reported
            } else if (reportErrors) {
              Error(tailCall.Tok, "a recursive call inside a loop is not recognized as being a tail call");
            }
            return TailRecursionStatus.NotTailRecursive;
          }
        }
      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        var status = TailRecursionStatus.NotTailRecursive;
        if (s.Body != null) {
          status = CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
        if (status != TailRecursionStatus.CanBeFollowedByAnything) {
          if (status == TailRecursionStatus.NotTailRecursive) {
            // an error has already been reported
          } else if (reportErrors) {
            Error(tailCall.Tok, "a recursive call inside a forall statement is not a tail call");
          }
          return TailRecursionStatus.NotTailRecursive;
        }
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        var status = TailRecursionStatus.CanBeFollowedByAnything;
        foreach (var kase in s.Cases) {
          var st = CheckTailRecursive(kase.Body, enclosingMethod, ref tailCall, reportErrors);
          if (st == TailRecursionStatus.NotTailRecursive) {
            return st;
          } else if (st == TailRecursionStatus.TailCallSpent) {
            status = st;
          }
        }
        return status;
      } else if (stmt is AssignSuchThatStmt) {
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        return CheckTailRecursive(s.ResolvedStatements, enclosingMethod, ref tailCall, reportErrors);
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Update != null) {
          return CheckTailRecursive(s.Update, enclosingMethod, ref tailCall, reportErrors);
        }
      } else {
        Contract.Assert(false);  // unexpected statement type
      }
      return TailRecursionStatus.CanBeFollowedByAnything;
    }
    #endregion CheckTailRecursive

    // ------------------------------------------------------------------------------------------------------
    // ----- CoPredicateChecks ------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CoPredicateChecks
    enum CallingPosition { Positive, Negative, Neither }
    static CallingPosition Invert(CallingPosition cp) {
      switch (cp) {
        case CallingPosition.Positive: return CallingPosition.Negative;
        case CallingPosition.Negative: return CallingPosition.Positive;
        default: return CallingPosition.Neither;
      }
    }

    class CoPredicateChecks_Visitor : ResolverTopDownVisitor<CallingPosition>
    {
      public readonly CoPredicate context;
      public CoPredicateChecks_Visitor(Resolver resolver, CoPredicate context)
        : base(resolver)
      {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }

      protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            // we're looking at a recursive call
            if (!(e.Function is CoPredicate)) {
              Error(e, "a recursive call from a copredicate can go only to other copredicates");
            } else if (cp != CallingPosition.Positive) {
              var msg = "a copredicate can be called recursively only in positive positions";
              if (cp == CallingPosition.Neither) {
                // this may be inside an existential quantifier
                msg += " and cannot sit inside an unbounded existential quantifier";
              } else {
                // the co-call is not inside an existential quantifier, so don't bother mentioning the part of existentials in the error message
              }
              Error(e, msg);
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.Yes;
              ReportAdditionalInformation(e.tok, e.Function.Name + "#[_k - 1]", e.Function.Name.Length);
            }
          }
          // fall through to do the subexpressions (with cp := Neither)
        } else if (expr is UnaryOpExpr) {
          var e = (UnaryOpExpr)expr;
          if (e.Op == UnaryOpExpr.Opcode.Not) {
            // for the sub-parts, use Invert(cp)
            cp = Invert(cp);
            return true;
          }
        } else if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          switch (e.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.And:
            case BinaryExpr.ResolvedOpcode.Or:
              return true;  // do the sub-parts with the same "cp"
            case BinaryExpr.ResolvedOpcode.Imp:
              Visit(e.E0, Invert(cp));
              Visit(e.E1, cp);
              return false;  // don't recurse (again) on the sub-parts
            default:
              break;
          }
        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          Visit(e.Source, CallingPosition.Neither);
          var theCp = cp;
          e.Cases.Iter(kase => Visit(kase.Body, theCp));
          return false;
        } else if (expr is ITEExpr) {
          var e = (ITEExpr)expr;
          Visit(e.Test, CallingPosition.Neither);
          Visit(e.Thn, cp);
          Visit(e.Els, cp);
          return false;
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var rhs in e.RHSs) {
            Visit(rhs, CallingPosition.Neither);
          }
          // note, a let-such-that expression introduces an existential that may depend on the _k in a copredicate, so we disallow recursive copredicate calls in the body of the let-such-that
          Visit(e.Body, e.Exact ? cp : CallingPosition.Neither);
          return false;
        } else if (expr is QuantifierExpr) {
          var e = (QuantifierExpr)expr;
          if ((cp == CallingPosition.Positive && e is ExistsExpr) || (cp == CallingPosition.Negative && e is ForallExpr)) {
            if (e.MissingBounds != null && e.MissingBounds.Count != 0) {
              // Don't allow any co-recursive calls under an existential with an unbounded range, because that can be unsound.
              cp = CallingPosition.Neither;
            }
          }
          Visit(e.LogicalBody(), cp);
          return false;
        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          Visit(e.E, cp);
          Visit(e.S, CallingPosition.Neither);
          return false;
        } else if (expr is ConcreteSyntaxExpression) {
          // do the sub-parts with the same "cp"
          return true;
        }
        // do the sub-parts with cp := Neither
        cp = CallingPosition.Neither;
        return true;
      }

      protected override bool VisitOneStmt(Statement stmt, ref CallingPosition st) {
        if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          if (ModuleDefinition.InSameSCC(context, s.Method)) {
            // we're looking at a recursive call
            Error(stmt.Tok, "a recursive call from a copredicate can go only to other copredicates");
          }
          // do the sub-parts with the same "cp"
          return true;
        } else {
          return base.VisitOneStmt(stmt, ref st);
        }
      }
    }

    void CoPredicateChecks(Expression expr, CoPredicate context, CallingPosition cp) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);
      var v = new CoPredicateChecks_Visitor(this, context);
      v.Visit(expr, cp);
    }
    #endregion CoPredicateChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- CoLemmaChecks ----------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CoLemmaChecks
    class CoLemmaChecks_Visitor : ResolverBottomUpVisitor
    {
      CoLemma context;
      public CoLemmaChecks_Visitor(Resolver resolver, CoLemma context)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          if (s.Method is CoLemma || s.Method is PrefixLemma) {
            // all is cool
          } else {
            // the call goes from a colemma context to a non-colemma callee
            if (ModuleDefinition.InSameSCC(context, s.Method)) {
              // we're looking at a recursive call (to a non-colemma)
              Error(s.Tok, "a recursive call from a colemma can go only to other colemmas and prefix lemmas");
            }
          }
        }
      }
      protected override void VisitOneExpr(Expression expr)
      {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          // the call goes from a colemma context to a non-colemma callee
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            // we're looking at a recursive call (to a non-colemma)
            Error(e.tok, "a recursive call from a colemma can go only to other colemmas and prefix lemmas");
          }
        }
      }
    }
    void CoLemmaChecks(Statement stmt, CoLemma context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);
      var v = new CoLemmaChecks_Visitor(this, context);
      v.Visit(stmt);
    }
    #endregion CoLemmaChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckEqualityTypes -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CheckEqualityTypes
    class CheckEqualityTypes_Visitor : ResolverTopDownVisitor<bool>
    {
      public CheckEqualityTypes_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override bool VisitOneStmt(Statement stmt, ref bool st) {
        if (stmt.IsGhost) {
          return false;  // no need to recurse to sub-parts, since all sub-parts must be ghost as well
        } else if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          foreach (var v in s.Locals) {
            CheckEqualityTypes_Type(v.Tok, v.Type);
          }
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          // don't recurse on the specification parts, which are ghost
          if (s.Guard != null) {
            Visit(s.Guard, st);
          }
          // don't recurse on the body, if it's a dirty loop
          if (s.Body != null) {
            Visit(s.Body, st);
          }
          return false;
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          // don't recurse on the specification parts, which are ghost
          foreach (var alt in s.Alternatives) {
            Visit(alt.Guard, st);
            foreach (var ss in alt.Body) {
              Visit(ss, st);
            }
          }
          return false;
        } else if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          Contract.Assert(s.Method.TypeArgs.Count <= s.MethodSelect.TypeArgumentSubstitutions().Count);
          var i = 0;
          foreach (var formalTypeArg in s.Method.TypeArgs) {
            var actualTypeArg = s.MethodSelect.TypeArgumentSubstitutions()[formalTypeArg];
            if (formalTypeArg.MustSupportEquality && !actualTypeArg.SupportsEquality) {
              Error(s.Tok, "type parameter {0} ({1}) passed to method {2} must support equality (got {3}){4}", i, formalTypeArg.Name, s.Method.Name, actualTypeArg, TypeEqualityErrorMessageHint(actualTypeArg));
            }
            i++;
          }
          // recursively visit all subexpressions (which are all actual parameters) passed in for non-ghost formal parameters
          Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);
          i = 0;
          foreach (var ee in s.Lhs) {
            if (!s.Method.Outs[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          Visit(s.Receiver, st);
          Contract.Assert(s.Args.Count == s.Method.Ins.Count);
          i = 0;
          foreach (var ee in s.Args) {
            if (!s.Method.Ins[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          return false;  // we've done what there is to be done
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          foreach (var v in s.BoundVars) {
            CheckEqualityTypes_Type(v.Tok, v.Type);
          }
        }
        return true;
      }
      protected override bool VisitOneExpr(Expression expr, ref bool st) {
        if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          var t0 = e.E0.Type.NormalizeExpand();
          var t1 = e.E1.Type.NormalizeExpand();
          switch (e.Op) {
            case BinaryExpr.Opcode.Eq:
            case BinaryExpr.Opcode.Neq:
              // First, check a special case:  a datatype value (like Nil) that takes no parameters
              var e0 = e.E0.Resolved as DatatypeValue;
              var e1 = e.E1.Resolved as DatatypeValue;
              if (e0 != null && e0.Arguments.Count == 0) {
                // that's cool
              } else if (e1 != null && e1.Arguments.Count == 0) {
                // oh yeah!
              } else if (!t0.SupportsEquality) {
                Error(e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
              } else if (!t1.SupportsEquality) {
                Error(e.E1, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
              }
              break;
            default:
              switch (e.ResolvedOp) {
                // Note, all operations on sets, multisets, and maps are guaranteed to work because of restrictions placed on how
                // these types are instantiated.  (Except: This guarantee does not apply to equality on maps, because the Range type
                // of maps is not restricted, only the Domain type.  However, the equality operator is checked above.)
                case BinaryExpr.ResolvedOpcode.InSeq:
                case BinaryExpr.ResolvedOpcode.NotInSeq:
                case BinaryExpr.ResolvedOpcode.Prefix:
                case BinaryExpr.ResolvedOpcode.ProperPrefix:
                  if (!t1.SupportsEquality) {
                    Error(e.E1, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
                  } else if (!t0.SupportsEquality) {
                    if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSeq) {
                      Error(e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                    } else {
                      Error(e.E0, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                    }
                  }
                  break;
                default:
                  break;
              }
              break;
          }
        } else if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          foreach (var bv in e.BoundVars) {
            CheckEqualityTypes_Type(bv.tok, bv.Type);
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var bv in e.BoundVars) {
            CheckEqualityTypes_Type(bv.tok, bv.Type);
          }
        } else if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          Contract.Assert(e.Function.TypeArgs.Count <= e.TypeArgumentSubstitutions.Count);
          var i = 0;
          foreach (var formalTypeArg in e.Function.TypeArgs) {
            var actualTypeArg = e.TypeArgumentSubstitutions[formalTypeArg];
            if (formalTypeArg.MustSupportEquality && !actualTypeArg.SupportsEquality) {
              Error(e.tok, "type parameter {0} ({1}) passed to function {2} must support equality (got {3}){4}", i, formalTypeArg.Name, e.Function.Name, actualTypeArg, TypeEqualityErrorMessageHint(actualTypeArg));
            }
            i++;
          }
          // recursively visit all subexpressions (which are all actual parameters) passed in for non-ghost formal parameters
          Visit(e.Receiver, st);
          Contract.Assert(e.Args.Count == e.Function.Formals.Count);
          i = 0;
          foreach (var ee in e.Args) {
            if (!e.Function.Formals[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          return false;  // we've done what there is to be done
        } else if (expr is SetDisplayExpr || expr is MultiSetDisplayExpr || expr is MapDisplayExpr || expr is MultiSetFormingExpr) {
          // This catches other expressions whose type may potentially be illegal
          CheckEqualityTypes_Type(expr.tok, expr.Type);
        }
        return true;
      }

      public void CheckEqualityTypes_Type(IToken tok, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(type != null);
        type = type.NormalizeExpand();
        if (type is BasicType) {
          // fine
        } else if (type is SetType) {
          var argType = ((SetType)type).Arg;
          if (!argType.SupportsEquality) {
            Error(tok, "set argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType));
          }
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is MultiSetType) {
          var argType = ((MultiSetType)type).Arg;
          if (!argType.SupportsEquality) {
            Error(tok, "multiset argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType));
          }
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is MapType) {
          var mt = (MapType)type;
          if (!mt.Finite) {
            Error(tok, "imaps do not support equality: {0}", mt);
          }
          if (!mt.Domain.SupportsEquality) {
            Error(tok, "map domain type must support equality (got {0}){1}", mt.Domain, TypeEqualityErrorMessageHint(mt.Domain));
          }
          CheckEqualityTypes_Type(tok, mt.Domain);
          CheckEqualityTypes_Type(tok, mt.Range);

        } else if (type is SeqType) {
          Type argType = ((SeqType)type).Arg;
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is UserDefinedType) {
          var udt = (UserDefinedType)type;
          List<TypeParameter> formalTypeArgs = null;
          if (udt.ResolvedClass != null) {
            formalTypeArgs = udt.ResolvedClass.TypeArgs;
          } else if (udt.ResolvedParam is OpaqueType_AsParameter) {
            var t = (OpaqueType_AsParameter)udt.ResolvedParam;
            formalTypeArgs = t.TypeArgs;
          }
          if (formalTypeArgs == null) {
            Contract.Assert(udt.TypeArgs.Count == 0);
          } else {
            Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
            var i = 0;
            foreach (var argType in udt.TypeArgs) {
              var formalTypeArg = formalTypeArgs[i];
              if (formalTypeArg.MustSupportEquality && !argType.SupportsEquality) {
                Error(tok, "type parameter {0} ({1}) passed to type {2} must support equality (got {3}){4}", i, formalTypeArg.Name, udt.ResolvedClass.Name, argType, TypeEqualityErrorMessageHint(argType));
              }
              CheckEqualityTypes_Type(tok, argType);
              i++;
            }
          }

        } else if (type is TypeProxy) {
          // the type was underconstrained; this is checked elsewhere, but it is not in violation of the equality-type test
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
        }
      }

      string TypeEqualityErrorMessageHint(Type argType) {
        Contract.Requires(argType != null);
        var tp = argType.AsTypeParameter;
        if (tp != null) {
          return string.Format(" (perhaps try declaring type parameter '{0}' on line {1} as '{0}(==)', which says it can only be instantiated with a type that supports equality)", tp.Name, tp.tok.line);
        }
        return "";
      }
    }
    void CheckEqualityTypes_Stmt(Statement stmt) {
      Contract.Requires(stmt != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.Visit(stmt, false);
    }
    void CheckEqualityTypes(Expression expr) {
      Contract.Requires(expr != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.Visit(expr, false);
    }
    public void CheckEqualityTypes_Type(IToken tok, Type type) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.CheckEqualityTypes_Type(tok, type);
    }

    #endregion CheckEqualityTypes

    // ------------------------------------------------------------------------------------------------------
    // ----- FillInDefaultLoopDecreases ---------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region FillInDefaultLoopDecreases
    class FillInDefaultLoopDecreases_Visitor : ResolverBottomUpVisitor
    {
      readonly ICallable EnclosingMethod;
      public FillInDefaultLoopDecreases_Visitor(Resolver resolver, ICallable enclosingMethod)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(enclosingMethod != null);
        EnclosingMethod = enclosingMethod;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          resolver.FillInDefaultLoopDecreases(s, s.Guard, s.Decreases.Expressions, EnclosingMethod);
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          resolver.FillInDefaultLoopDecreases(s, null, s.Decreases.Expressions, EnclosingMethod);
        }
      }
    }
    #endregion FillInDefaultLoopDecreases

    // ------------------------------------------------------------------------------------------------------
    // ----- ReportMoreAdditionalInformation ----------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region ReportOtherAdditionalInformation_Visitor
    class ReportOtherAdditionalInformation_Visitor : ResolverBottomUpVisitor
    {
      public ReportOtherAdditionalInformation_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          if (s.Kind == ForallStmt.ParBodyKind.Call) {
            var cs = (CallStmt)s.S0;
            // show the callee's postcondition as the postcondition of the 'forall' statement
            // TODO:  The following substitutions do not correctly take into consideration variable capture; hence, what the hover text displays may be misleading
            var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
            Contract.Assert(cs.Method.Ins.Count == cs.Args.Count);
            for (int i = 0; i < cs.Method.Ins.Count; i++) {
              argsSubstMap.Add(cs.Method.Ins[i], cs.Args[i]);
            }
            var substituter = new Translator.AlphaConverting_Substituter(cs.Receiver, argsSubstMap, new Dictionary<TypeParameter, Type>(), new Translator());
            foreach (var ens in cs.Method.Ens) {
              var p = substituter.Substitute(ens.E);  // substitute the call's actuals for the method's formals
              resolver.ReportAdditionalInformation(s.Tok, "ensures " + Printer.ExprToString(p) + ";", s.Tok.val.Length);
            }
          }
        }
      }
    }
    #endregion ReportOtherAdditionalInformation_Visitor

    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------

    bool InferRequiredEqualitySupport(TypeParameter tp, Type type) {
      Contract.Requires(tp != null);
      Contract.Requires(type != null);

      type = type.NormalizeExpand();
      if (type is BasicType) {
      } else if (type is SetType) {
        var st = (SetType)type;
        return st.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, st.Arg);
      } else if (type is MultiSetType) {
        var ms = (MultiSetType)type;
        return ms.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, ms.Arg);
      } else if (type is MapType) {
        var mt = (MapType)type;
        return mt.Domain.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, mt.Domain) || InferRequiredEqualitySupport(tp, mt.Range);
      } else if (type is SeqType) {
        var sq = (SeqType)type;
        return InferRequiredEqualitySupport(tp, sq.Arg);
      } else if (type is UserDefinedType) {
        var udt = (UserDefinedType)type;
        List<TypeParameter> formalTypeArgs = null;
        if (udt.ResolvedClass != null) {
          formalTypeArgs = udt.ResolvedClass.TypeArgs;
        } else if (udt.ResolvedParam is OpaqueType_AsParameter) {
          var t = (OpaqueType_AsParameter)udt.ResolvedParam;
          formalTypeArgs = t.TypeArgs;
        }
        if (formalTypeArgs == null) {
          Contract.Assert(udt.TypeArgs.Count == 0);
        } else {
          Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
          var i = 0;
          foreach (var argType in udt.TypeArgs) {
            var formalTypeArg = formalTypeArgs[i];
            if ((formalTypeArg.MustSupportEquality && argType.AsTypeParameter == tp) || InferRequiredEqualitySupport(tp, argType)) {
              return true;
            }
            i++;
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return false;
    }

    ClassDecl currentClass;
    Method currentMethod;
    readonly Scope<TypeParameter>/*!*/ allTypeParameters = new Scope<TypeParameter>();
    readonly Scope<IVariable>/*!*/ scope = new Scope<IVariable>();
    Scope<Statement>/*!*/ labeledStatements = new Scope<Statement>();
    List<Statement> loopStack = new List<Statement>();  // the enclosing loops (from which it is possible to break out)
    readonly Dictionary<Statement, bool> inSpecOnlyContext = new Dictionary<Statement, bool>();  // invariant: domain contain union of the domains of "labeledStatements" and "loopStack"


    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveClassMemberTypes(ClassDecl cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;

      // Resolve names of traits extended
      if (cl.TraitsTyp != null)
      {
          cl.TraitsObj = new List<TraitDecl>();
          foreach (Type traitTyp in cl.TraitsTyp)
          {
              if (traitTyp is UserDefinedType)
              {
                  var trait = classMembers.Keys.FirstOrDefault(traitDecl => traitDecl.CompileName == ((UserDefinedType)(traitTyp)).FullCompileName);
                  if (trait == null)
                  {
                      Error(((UserDefinedType)(traitTyp)).tok, "unresolved identifier: {0}", ((UserDefinedType)(traitTyp)).tok.val);
                  }
                  else if (!(trait is TraitDecl))
                  {
                      Error(((UserDefinedType)(traitTyp)).tok, "identifier '{0}' does not denote a trait", ((UserDefinedType)(traitTyp)).tok.val);
                  }
                  else
                  {
                      //disallowing inheritance in multi module case
                      string clModName = cl.Module.CompileName.Replace("_Compile", string.Empty);
                      string traitModName = trait.Module.CompileName.Replace("_Compile", string.Empty);
                      if (clModName != traitModName)
                      {
                          Error(((UserDefinedType)(traitTyp)).tok, string.Format("class {0} is in a different module than trait {1}. A class may only extend a trait in the same module",
                            cl.FullName, trait.FullName));
                      }
                      else
                      {
                          cl.TraitsObj.Add((TraitDecl)trait);
                      }
                  }
              }
          }
      }

      foreach (MemberDecl member in cl.Members) {
        member.EnclosingClass = cl;
        if (member is Field) {
          // In the following, we pass in a NoContext, because any cycle formed by newtype constraints would have to
          // involve a non-null object in order to get to the field and its type, and there is no way in a newtype constraint
          // to obtain a non-null object.
          ResolveType(member.tok, ((Field)member).Type, new NoContext(cl.Module), ResolveTypeOptionEnum.DontInfer, null);

        } else if (member is Function) {
          var f = (Function)member;
          var ec = ErrorCount;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, true, f);
          ResolveFunctionSignature(f);
          allTypeParameters.PopMarker();
          if (f is CoPredicate && ec == ErrorCount) {
            var ff = ((CoPredicate)f).PrefixPredicate;
            ff.EnclosingClass = cl;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(ff.TypeArgs, true, ff);
            ResolveFunctionSignature(ff);
            allTypeParameters.PopMarker();
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = ErrorCount;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, true, m);
          ResolveMethodSignature(m);
          allTypeParameters.PopMarker();
          var com = m as CoLemma;
          if (com != null && com.PrefixLemma != null && ec == ErrorCount) {
            var mm = com.PrefixLemma;
            // resolve signature of the prefix lemma
            mm.EnclosingClass = cl;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(mm.TypeArgs, true, mm);
            ResolveMethodSignature(mm);
            allTypeParameters.PopMarker();
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }

      currentClass = null;
    }

    void InheritTraitMembers(ClassDecl cl) {
      Contract.Requires(cl != null);

      RefinementCloner cloner = new RefinementCloner(cl.Module);
      //merging class members with parent members if any
      if (cl.TraitsObj != null) {
        var clMembers = classMembers[cl];
        foreach (TraitDecl traitObj in cl.TraitsObj)
        {
            var traitMembers = classMembers[traitObj];
            //merging current class members with the inheriting trait
            foreach (KeyValuePair<string, MemberDecl> traitMem in traitMembers)
            {
                MemberDecl clMember;
                if (clMembers.TryGetValue(traitMem.Key, out clMember))
                {
                    //check if the signature of the members are equal and the member is body-less
                    if (traitMem.Value is Method)
                    {
                        Method traitMethod = (Method)traitMem.Value;
                        // TODO: should check that the class member is also a method, and the same kind of method
                        Method classMethod = (Method)clMember;
                        //refinementTransformer.CheckMethodsAreRefinements(classMethod, traitMethod);
                        if (traitMethod.Body != null && !clMembers[classMethod.CompileName].Inherited) //if the existing method in the class is not that inherited one from the parent
                            Error(classMethod, "a class cannot override implemented methods");
                        else
                        {
                            classMethod.OverriddenMethod = traitMethod;
                            //adding a call graph edge from the trait method to that of class
                            cl.Module.CallGraph.AddEdge(traitMethod, classMethod);

                            //checking specifications
                            //class method must provide its own specifications in case the overriden method has provided any
                            if ((classMethod.Req == null || classMethod.Req.Count == 0) && (classMethod.OverriddenMethod.Req != null && classMethod.OverriddenMethod.Req.Count > 0))  //it means m.OverriddenMethod.Req =>  m.Req
                            {
                                Error(classMethod, "Method must provide its own Requires clauses anew");
                            }
                            if ((classMethod.Ens == null || classMethod.Ens.Count == 0) && (classMethod.OverriddenMethod.Ens != null && classMethod.OverriddenMethod.Ens.Count > 0))  //it means m.OverriddenMethod.Ens =>  m.Ens
                            {
                                Error(classMethod, "Method must provide its own Ensures clauses anew");
                            }
                            if ((classMethod.Mod == null || classMethod.Mod.Expressions == null || classMethod.Mod.Expressions.Count == 0) && (classMethod.OverriddenMethod.Mod != null && classMethod.OverriddenMethod.Mod.Expressions != null && classMethod.OverriddenMethod.Mod.Expressions.Count > 0))  //it means m.OverriddenMethod.Mod =>  m.Mod
                            {
                                Error(classMethod, "Method must provide its own Modifies clauses anew");
                            }
                            if ((classMethod.Decreases == null || classMethod.Decreases.Expressions == null || classMethod.Decreases.Expressions.Count == 0) && (classMethod.OverriddenMethod.Decreases != null && classMethod.OverriddenMethod.Decreases.Expressions != null && classMethod.OverriddenMethod.Decreases.Expressions.Count > 0))  //it means m.OverriddenMethod.Decreases =>  m.Decreases
                            {
                                Error(classMethod, "Method must provide its own Decreases clauses anew");
                            }
                        }
                    }
                    else if (traitMem.Value is Function)
                    {
                        Function traitFunction = (Function)traitMem.Value;
                        Function classFunction = (Function)clMember;
                        //refinementTransformer.CheckFunctionsAreRefinements(classFunction, traitFunction);
                        if (traitFunction.Body != null && !classMembers[cl][classFunction.CompileName].Inherited)
                            Error(classFunction, "a class cannot override implemented functions");
                        else
                        {
                            classFunction.OverriddenFunction = traitFunction;
                            //adding a call graph edge from the trait function to that of class
                            cl.Module.CallGraph.AddEdge(traitFunction, classFunction);

                            //checking specifications
                            //class function must provide its own specifications in case the overriden function has provided any
                            if ((classFunction.Req == null || classFunction.Req.Count == 0) && (classFunction.OverriddenFunction.Req != null && classFunction.OverriddenFunction.Req.Count > 0))  //it means m.OverriddenMethod.Req =>  m.Req
                            {
                                Error(classFunction, "Function must provide its own Requires clauses anew");
                            }
                            if ((classFunction.Ens == null || classFunction.Ens.Count == 0) && (classFunction.OverriddenFunction.Ens != null && classFunction.OverriddenFunction.Ens.Count > 0))  //it means m.OverriddenMethod.Ens =>  m.Ens
                            {
                                Error(classFunction, "Function must provide its own Ensures clauses anew");
                            }
                            if ((classFunction.Reads == null || classFunction.Reads.Count == 0) && (classFunction.OverriddenFunction.Reads != null && classFunction.OverriddenFunction.Reads.Count > 0))  //it means m.OverriddenMethod.Mod =>  m.Mod
                            {
                                Error(classFunction, "Function must provide its own Reads clauses anew");
                            }
                            if ((classFunction.Decreases == null || classFunction.Decreases.Expressions == null || classFunction.Decreases.Expressions.Count == 0) && (classFunction.OverriddenFunction.Decreases != null && classFunction.OverriddenFunction.Decreases.Expressions != null && classFunction.OverriddenFunction.Decreases.Expressions.Count > 0))  //it means m.OverriddenMethod.Decreases =>  m.Decreases
                            {
                                Error(classFunction, "Function must provide its own Decreases clauses anew");
                            }
                        }
                    }
                    else if (traitMem.Value is Field)
                    {
                        Field traitField = (Field)traitMem.Value;
                        Field classField = (Field)clMember;
                        if (!clMembers[classField.CompileName].Inherited)
                            Error(classField, "member in the class has been already inherited from its parent trait");
                    }
                }
                else
                {
                    //the member is not already in the class
                    // enter the trait member in the symbol table for the class
                    MemberDecl classNewMember = cloner.CloneMember(traitMem.Value);
                    classNewMember.EnclosingClass = cl;
                    classNewMember.Inherited = true;
                    classMembers[cl].Add(traitMem.Key, classNewMember);
                    cl.Members.Add(classNewMember);
                }
            }//foreach
        }
        //checking to make sure all body-less methods/functions have been implemented in the child class
        if (refinementTransformer == null)
          refinementTransformer = new RefinementTransformer(this, AdditionalInformationReporter, null);
        foreach (TraitDecl traitObj in cl.TraitsObj)
        {
            foreach (MemberDecl traitMember in traitObj.Members.Where(mem => mem is Function || mem is Method))
            {
                if (traitMember is Function)
                {
                    Function traitFunc = (Function)traitMember;
                    if (traitFunc.Body == null) //we do this check only if trait function body is null
                    {
                        var classMem = cl.Members.Where(clMem => clMem is Function).FirstOrDefault(clMem => ((Function)clMem).Body != null && clMem.CompileName == traitMember.CompileName);
                        if (classMem != null)
                        {
                            Function classFunc = (Function)classMem;
                            refinementTransformer.CheckOverride_FunctionParameters(classFunc, traitFunc);
                        }
                        else if (!cl.Module.IsAbstract && traitFunc.Body == null && classMem == null)
                            Error(cl, "class: {0} does not implement trait member: {1}", cl.CompileName, traitFunc.CompileName);
                    }
                }
                if (traitMember is Method)
                {
                    Method traitMethod = (Method)traitMember;
                    if (traitMethod.Body == null) //we do this check only if trait method body is null
                    {
                        var classMem = cl.Members.Where(clMem => clMem is Method).FirstOrDefault(clMem => ((Method)clMem).Body != null && clMem.CompileName == traitMember.CompileName);
                        if (classMem != null)
                        {
                            Method classMethod = (Method)classMem;
                            refinementTransformer.CheckOverride_MethodParameters(classMethod, traitMethod);
                        }
                        if (!cl.Module.IsAbstract && traitMethod.Body == null && classMem == null)
                            Error(cl, "class: {0} does not implement trait member: {1}", cl.CompileName, traitMethod.CompileName);
                    }
                }
            }
        }
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed, and that all types in class members have been resolved
    /// </summary>
    void ResolveClassMemberBodies(ClassDecl cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        if (member is Field) {
          ResolveAttributes(member.Attributes, new ResolveOpts(new NoContext(currentClass.Module), false));
          // nothing more to do

        } else if (member is Function) {
          var f = (Function)member;
          var ec = ErrorCount;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, false, f);
          ResolveFunction(f);
          allTypeParameters.PopMarker();
          if (f is CoPredicate && ec == ErrorCount) {
            var ff = ((CoPredicate)f).PrefixPredicate;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(ff.TypeArgs, false, ff);
            ResolveFunction(ff);
            allTypeParameters.PopMarker();
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = ErrorCount;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, false, m);
          ResolveMethod(m);
          allTypeParameters.PopMarker();

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }
      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveCtorTypes(DatatypeDecl/*!*/ dt, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ coDependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(dependencies != null);
      Contract.Requires(coDependencies != null);
      foreach (DatatypeCtor ctor in dt.Ctors) {

        ctor.EnclosingDatatype = dt;

        allTypeParameters.PushMarker();
        ResolveCtorSignature(ctor, dt.TypeArgs);
        allTypeParameters.PopMarker();

        if (dt is IndDatatypeDecl) {
          // The dependencies of interest among inductive datatypes are all (inductive data)types mentioned in the parameter types
          var idt = (IndDatatypeDecl)dt;
          dependencies.AddVertex(idt);
          foreach (Formal p in ctor.Formals) {
            AddDatatypeDependencyEdge(idt, p.Type, dependencies);
          }
        } else {
          // The dependencies of interest among codatatypes are just the top-level types of parameters.
          var codt = (CoDatatypeDecl)dt;
          coDependencies.AddVertex(codt);
          foreach (var p in ctor.Formals) {
            var co = p.Type.AsCoDatatype;
            if (co != null && codt.Module == co.Module) {
              coDependencies.AddEdge(codt, co);
            }
          }
        }
      }
    }

    void AddDatatypeDependencyEdge(IndDatatypeDecl dt, Type tp, Graph<IndDatatypeDecl> dependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(tp != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      tp = tp.NormalizeExpand();
      var dependee = tp.AsIndDatatype;
      if (dependee != null && dt.Module == dependee.Module) {
        dependencies.AddEdge(dt, dependee);
        foreach (var ta in ((UserDefinedType)tp).TypeArgs) {
          AddDatatypeDependencyEdge(dt, ta, dependencies);
        }
      }
    }

    /// <summary>
    /// Check that the SCC of 'startingPoint' can be carved up into stratospheres in such a way that each
    /// datatype has some value that can be constructed from datatypes in lower stratospheres only.
    /// The algorithm used here is quadratic in the number of datatypes in the SCC.  Since that number is
    /// deemed to be rather small, this seems okay.
    ///
    /// As a side effect of this checking, the DefaultCtor field is filled in (for every inductive datatype
    /// that passes the check).  It may be that several constructors could be used as the default, but
    /// only the first one encountered as recorded.  This particular choice is slightly more than an
    /// implementation detail, because it affects how certain cycles among inductive datatypes (having
    /// to do with the types used to instantiate type parameters of datatypes) are used.
    ///
    /// The role of the SCC here is simply to speed up this method.  It would still be correct if the
    /// equivalence classes in the given SCC were unions of actual SCC's.  In particular, this method
    /// would still work if "dependencies" consisted of one large SCC containing all the inductive
    /// datatypes in the module.
    /// </summary>
    void SccStratosphereCheck(IndDatatypeDecl startingPoint, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies) {
      Contract.Requires(startingPoint != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      var scc = dependencies.GetSCC(startingPoint);
      int totalCleared = 0;
      while (true) {
        int clearedThisRound = 0;
        foreach (var dt in scc) {
          if (dt.DefaultCtor != null) {
            // previously cleared
          } else if (ComputeDefaultCtor(dt)) {
            Contract.Assert(dt.DefaultCtor != null);  // should have been set by the successful call to StratosphereCheck)
            clearedThisRound++;
            totalCleared++;
          }
        }
        if (totalCleared == scc.Count) {
          // all is good
          return;
        } else if (clearedThisRound != 0) {
          // some progress was made, so let's keep going
        } else {
          // whatever is in scc-cleared now failed to pass the test
          foreach (var dt in scc) {
            if (dt.DefaultCtor == null) {
              Error(dt, "because of cyclic dependencies among constructor argument types, no instances of datatype '{0}' can be constructed", dt.Name);
            }
          }
          return;
        }
      }
    }

    /// <summary>
    /// Check that the datatype has some constructor all whose argument types can be constructed.
    /// Returns 'true' and sets dt.DefaultCtor if that is the case.
    /// </summary>
    bool ComputeDefaultCtor(IndDatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(dt.DefaultCtor == null);  // the intention is that this method be called only when DefaultCtor hasn't already been set
      Contract.Ensures(!Contract.Result<bool>() || dt.DefaultCtor != null);

      // Stated differently, check that there is some constuctor where no argument type goes to the same stratum.
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var typeParametersUsed = new List<TypeParameter>();
        foreach (Formal p in ctor.Formals) {
          if (!CheckCanBeConstructed(p.Type, typeParametersUsed)) {
            // the argument type (has a component which) is not yet known to be constructable
            goto NEXT_OUTER_ITERATION;
          }
        }
        // this constructor satisfies the requirements, so the datatype is allowed
        dt.DefaultCtor = ctor;
        dt.TypeParametersUsedInConstructionByDefaultCtor = new bool[dt.TypeArgs.Count];
        for (int i = 0; i < dt.TypeArgs.Count; i++) {
          dt.TypeParametersUsedInConstructionByDefaultCtor[i] = typeParametersUsed.Contains(dt.TypeArgs[i]);
        }
        return true;
      NEXT_OUTER_ITERATION: { }
      }
      // no constructor satisfied the requirements, so this is an illegal datatype declaration
      return false;
    }

    bool CheckCanBeConstructed(Type tp, List<TypeParameter> typeParametersUsed) {
      tp = tp.NormalizeExpand();
      var dependee = tp.AsIndDatatype;
      if (dependee == null) {
        // the type is not an inductive datatype, which means it is always possible to construct it
        if (tp.IsTypeParameter) {
          typeParametersUsed.Add(((UserDefinedType)tp).ResolvedParam);
        }
        return true;
      } else if (dependee.DefaultCtor == null) {
        // the type is an inductive datatype that we don't yet know how to construct
        return false;
      }
      // also check the type arguments of the inductive datatype
      Contract.Assert(((UserDefinedType)tp).TypeArgs.Count == dependee.TypeParametersUsedInConstructionByDefaultCtor.Length);
      var i = 0;
      foreach (var ta in ((UserDefinedType)tp).TypeArgs) {  // note, "tp" is known to be a UserDefinedType, because that follows from tp being an inductive datatype
        if (dependee.TypeParametersUsedInConstructionByDefaultCtor[i] && !CheckCanBeConstructed(ta, typeParametersUsed)) {
          return false;
        }
        i++;
      }
      return true;
    }

    void DetermineEqualitySupport(IndDatatypeDecl startingPoint, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies) {
      Contract.Requires(startingPoint != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      var scc = dependencies.GetSCC(startingPoint);
      // First, the simple case:  If any parameter of any inductive datatype in the SCC is of a codatatype type, then
      // the whole SCC is incapable of providing the equality operation.  Also, if any parameter of any inductive datatype
      // is a ghost, then the whole SCC is incapable of providing the equality operation.
      foreach (var dt in scc) {
        Contract.Assume(dt.EqualitySupport == IndDatatypeDecl.ES.NotYetComputed);
        foreach (var ctor in dt.Ctors) {
          foreach (var arg in ctor.Formals) {
            var anotherIndDt = arg.Type.AsIndDatatype;
            if (arg.IsGhost ||
                (anotherIndDt != null && anotherIndDt.EqualitySupport == IndDatatypeDecl.ES.Never) ||
                arg.Type.IsCoDatatype ||
                arg.Type.IsArrowType ||
                arg.Type.IsIMapType) {
              // arg.Type is known never to support equality
              // So, go around the entire SCC and record what we learnt
              foreach (var ddtt in scc) {
                ddtt.EqualitySupport = IndDatatypeDecl.ES.Never;
              }
              return;  // we are done
            }
          }
        }
      }

      // Now for the more involved case:  we need to determine which type parameters determine equality support for each datatype in the SCC
      // We start by seeing where each datatype's type parameters are used in a place known to determine equality support.
      bool thingsChanged = false;
      foreach (var dt in scc) {
        if (dt.TypeArgs.Count == 0) {
          // if the datatype has no type parameters, we certainly won't find any type parameters being used in the arguments types to the constructors
          continue;
        }
        foreach (var ctor in dt.Ctors) {
          foreach (var arg in ctor.Formals) {
            var typeArg = arg.Type.AsTypeParameter;
            if (typeArg != null) {
              typeArg.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
              thingsChanged = true;
            } else {
              var otherDt = arg.Type.AsIndDatatype;
              if (otherDt != null && otherDt.EqualitySupport == IndDatatypeDecl.ES.ConsultTypeArguments) {  // datatype is in a different SCC
                var otherUdt = (UserDefinedType)arg.Type.NormalizeExpand();
                var i = 0;
                foreach (var otherTp in otherDt.TypeArgs) {
                  if (otherTp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                    var tp = otherUdt.TypeArgs[i].AsTypeParameter;
                    if (tp != null) {
                      tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
                      thingsChanged = true;
                    }
                  }
                }
              }
            }
          }
        }
      }
      // Then we propagate this information up through the SCC
      while (thingsChanged) {
        thingsChanged = false;
        foreach (var dt in scc) {
          if (dt.TypeArgs.Count == 0) {
            // if the datatype has no type parameters, we certainly won't find any type parameters being used in the arguments types to the constructors
            continue;
          }
          foreach (var ctor in dt.Ctors) {
            foreach (var arg in ctor.Formals) {
              var otherDt = arg.Type.AsIndDatatype;
              if (otherDt != null && otherDt.EqualitySupport == IndDatatypeDecl.ES.NotYetComputed) { // otherDt lives in the same SCC
                var otherUdt = (UserDefinedType)arg.Type.NormalizeExpand();
                var i = 0;
                foreach (var otherTp in otherDt.TypeArgs) {
                  if (otherTp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                    var tp = otherUdt.TypeArgs[i].AsTypeParameter;
                    if (tp != null && !tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                      tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
                      thingsChanged = true;
                    }
                  }
                  i++;
                }
              }
            }
          }
        }
      }
      // Now that we have computed the .NecessaryForEqualitySupportOfSurroundingInductiveDatatype values, mark the datatypes as ones
      // where equality support should be checked by looking at the type arguments.
      foreach (var dt in scc) {
        dt.EqualitySupport = IndDatatypeDecl.ES.ConsultTypeArguments;
      }
    }

    void ResolveAttributes(Attributes attrs, ResolveOpts opts) {
      Contract.Requires(opts != null);
      Contract.Requires(opts.DontCareAboutCompilation);  // attributes are never compiled
      // order does not matter much for resolution, so resolve them in reverse order
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Args != null) {
          ResolveAttributeArgs(attrs.Args, opts, true);
        }
      }
    }

    void ResolveAttributeArgs(List<Expression> args, ResolveOpts opts, bool allowGhosts) {
      Contract.Requires(args != null);
      foreach (var arg in args) {
        Contract.Assert(arg != null);
        int prevErrors = ErrorCount;
        ResolveExpression(arg, opts);
        if (!allowGhosts) {
          CheckIsNonGhost(arg);
        }
        if (prevErrors == ErrorCount) {
          CheckTypeInference(arg);
        }
      }
    }

    void ResolveTypeParameters(List<TypeParameter/*!*/>/*!*/ tparams, bool emitErrors, TypeParameter.ParentType/*!*/ parent) {
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push non-duplicated type parameter names
      int index = 0;
      foreach (TypeParameter tp in tparams) {
        if (emitErrors) {
          // we're seeing this TypeParameter for the first time
          tp.Parent = parent;
          tp.PositionalIndex = index;
        }
        if (!allTypeParameters.Push(tp.Name, tp) && emitErrors) {
          Error(tp, "Duplicate type-parameter name: {0}", tp.Name);
        }
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunctionSignature(Function f) {
      Contract.Requires(f != null);
      scope.PushMarker();
      if (f.SignatureIsOmitted) {
        Error(f, "function signature can be omitted only in refining functions");
      }
      var option = f.TypeArgs.Count == 0 ? new ResolveTypeOption(f) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      foreach (Formal p in f.Formals) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, f, option, f.TypeArgs);
      }
      ResolveType(f.tok, f.ResultType, f, option, f.TypeArgs);
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunction(Function f) {
      Contract.Requires(f != null);
      scope.PushMarker();
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }
      foreach (Formal p in f.Formals) {
        scope.Push(p.Name, p);
      }
      ResolveAttributes(f.Attributes, new ResolveOpts(f, false, true));
      foreach (Expression r in f.Req) {
        ResolveExpression(r, new ResolveOpts(f, false, true));
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Precondition must be a boolean (got {0})", r.Type);
        }
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, true, f.IsGhost, f);
      }
      foreach (Expression r in f.Ens) {
        ResolveExpression(r, new ResolveOpts(f, false, true));  // since this is a function, the postcondition is still a one-state predicate
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Postcondition must be a boolean (got {0})", r.Type);
        }
      }
      ResolveAttributes(f.Decreases.Attributes, new ResolveOpts(f, false, true));
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new ResolveOpts(f, false));
        // any type is fine
      }
      if (f.Body != null) {
        var prevErrorCount = ErrorCount;
        ResolveExpression(f.Body, new ResolveOpts(f, false));
        if (!f.IsGhost && prevErrorCount == ErrorCount) {
          CheckIsNonGhost(f.Body);
        }
        Contract.Assert(f.Body.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(f.Body.Type, f.ResultType)) {
          Error(f, "Function body type mismatch (expected {0}, got {1})", f.ResultType, f.Body.Type);
        }
      }
      scope.PopMarker();
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="fe"></param>
    /// <param name="readsFrame">True indicates "reads", false indicates "modifies".</param>
    /// <param name="isGhostContext"></param>
    /// <param name="codeContext"></param>
    void ResolveFrameExpression(FrameExpression fe, bool readsFrame, bool isGhostContext, ICodeContext codeContext) {
      Contract.Requires(fe != null);
      Contract.Requires(codeContext != null);
      ResolveExpression(fe.E, new ResolveOpts(codeContext, false, true /* yes, this is ghost */));
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      var arrTy = t.AsArrowType;
      if (arrTy != null) {
        t = arrTy.Result;
      }
      var collType = t.AsCollectionType;
      if (collType != null) {
        t = collType.Arg;
      }
      if (!UnifyTypes(t, new ObjectType())) {
        Error(fe.E, "a {0}-clause expression must denote an object or a collection of objects (instead got {1})", readsFrame ? "reads" : "modifies", fe.E.Type);
      } else if (fe.FieldName != null) {
        NonProxyType nptype;
        MemberDecl member = ResolveMember(fe.E.tok, t, fe.FieldName, out nptype);
        UserDefinedType ctype = (UserDefinedType)nptype;  // correctness of cast follows from the DenotesClass test above
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          Error(fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, ctype.Name);
        } else if (!readsFrame && isGhostContext && !member.IsGhost) {
          Error(fe.E, "in a ghost context, only ghost fields can be mentioned as modifies frame targets ({0})", fe.FieldName);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          fe.Field = (Field)member;
        }
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethodSignature(Method m) {
      Contract.Requires(m != null);
      scope.PushMarker();
      if (m.SignatureIsOmitted) {
        Error(m, "method signature can be omitted only in refining methods");
      }
      var option = m.TypeArgs.Count == 0 ? new ResolveTypeOption(m) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      // resolve in-parameters
      foreach (Formal p in m.Ins) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, m, option, m.TypeArgs);
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, m, option, m.TypeArgs);
      }
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);

      try
      {
        currentMethod = m;

        // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
        scope.PushMarker();
        if (m.IsStatic) {
          scope.AllowInstance = false;
        }
        foreach (Formal p in m.Ins) {
          scope.Push(p.Name, p);
        }

        // Start resolving specification...
        foreach (MaybeFreeExpression e in m.Req) {
          ResolveAttributes(e.Attributes, new ResolveOpts(m, false, true));
          ResolveExpression(e.E, new ResolveOpts(m, false, true));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.E.Type, Type.Bool)) {
            Error(e.E, "Precondition must be a boolean (got {0})", e.E.Type);
          }
        }
        ResolveAttributes(m.Mod.Attributes, new ResolveOpts(m, false, true));
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, false, m.IsGhost, m);
          if (m is Lemma) {
            Error(fe.tok, "lemmas are not allowed to have modifies clauses");
          } else if (m is CoLemma) {
            Error(fe.tok, "colemmas are not allowed to have modifies clauses");
          }
        }
        ResolveAttributes(m.Decreases.Attributes, new ResolveOpts(m, false, true));
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new ResolveOpts(m, false, true));
          // any type is fine
          if (m.IsGhost && e is WildcardExpr) {
            Error(e, "'decreases *' is not allowed on ghost methods");
          }
        }

        // Add out-parameters to a new scope that will also include the outermost-level locals of the body
        // Don't care about any duplication errors among the out-parameters, since they have already been reported
        scope.PushMarker();
        if (m is CoLemma && m.Outs.Count != 0) {
          Error(m.Outs[0].tok, "colemmas are not allowed to have out-parameters");
        } else {
          foreach (Formal p in m.Outs) {
            scope.Push(p.Name, p);
          }
        }

        // ... continue resolving specification
        foreach (MaybeFreeExpression e in m.Ens) {
          ResolveAttributes(e.Attributes, new ResolveOpts(m, true, true));
          ResolveExpression(e.E, new ResolveOpts(m, true, true));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.E.Type, Type.Bool)) {
            Error(e.E, "Postcondition must be a boolean (got {0})", e.E.Type);
          }
        }

        // Resolve body
        if (m.Body != null) {
          var com = m as CoLemma;
          if (com != null && com.PrefixLemma != null) {
            // The body may mentioned the implicitly declared parameter _k.  Throw it into the
            // scope before resolving the body.
            var k = com.PrefixLemma.Ins[0];
            scope.Push(k.Name, k);  // we expect no name conflict for _k
          }
          var codeContext = m;
          ResolveBlockStatement(m.Body, m.IsGhost, codeContext);
        }

        // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for colemmas)
        ResolveAttributes(m.Attributes, new ResolveOpts(m, false, true));

        scope.PopMarker();  // for the out-parameters and outermost-level locals
        scope.PopMarker();  // for the in-parameters
      }
      finally
      {
        currentMethod = null;
      }
    }

    void ResolveCtorSignature(DatatypeCtor ctor, List<TypeParameter> dtTypeArguments) {
      Contract.Requires(ctor != null);
      Contract.Requires(ctor.EnclosingDatatype != null);
      Contract.Requires(dtTypeArguments != null);
      foreach (Formal p in ctor.Formals) {
        // In the following, we pass in a NoContext, because any cycle formed by newtype constraints would have to
        // involve a non-null object in order to get to the field and its type, and there is no way in a newtype constraint
        // to obtain a non-null object.
        ResolveType(p.tok, p.Type, new NoContext(ctor.EnclosingDatatype.Module), ResolveTypeOptionEnum.AllowPrefix, dtTypeArguments);
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIteratorSignature(IteratorDecl iter) {
      Contract.Requires(iter != null);
      scope.PushMarker();
      if (iter.SignatureIsOmitted) {
        Error(iter, "iterator signature can be omitted only in refining methods");
      }
      var option = iter.TypeArgs.Count == 0 ? new ResolveTypeOption(iter) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      // resolve the types of the parameters
      foreach (var p in iter.Ins.Concat(iter.Outs)) {
        ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
      }
      // resolve the types of the added fields (in case some of these types would cause the addition of default type arguments)
      foreach (var p in iter.OutsHistoryFields) {
        ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
      }
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      var initialErrorCount = ErrorCount;

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      scope.PushMarker();
      scope.AllowInstance = false;  // disallow 'this' from use, which means that the special fields and methods added are not accessible in the syntactically given spec
      iter.Ins.ForEach(p => scope.Push(p.Name, p));

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolveOpts(iter, false, true));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        if (!UnifyTypes(d.Type, e.Type)) {
          // bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
          Error(e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
        }
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, true, false, iter);
      }
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, false, false, iter);
      }
      foreach (MaybeFreeExpression e in iter.Requires) {
        ResolveExpression(e.E, new ResolveOpts(iter, false, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Precondition must be a boolean (got {0})", e.E.Type);
        }
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (MaybeFreeExpression e in iter.YieldRequires) {
        ResolveExpression(e.E, new ResolveOpts(iter, false, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Yield precondition must be a boolean (got {0})", e.E.Type);
        }
      }
      foreach (MaybeFreeExpression e in iter.YieldEnsures) {
        ResolveExpression(e.E, new ResolveOpts(iter, true, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Yield postcondition must be a boolean (got {0})", e.E.Type);
        }
      }
      foreach (MaybeFreeExpression e in iter.Ensures) {
        ResolveExpression(e.E, new ResolveOpts(iter, true, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Postcondition must be a boolean (got {0})", e.E.Type);
        }
      }

      ResolveAttributes(iter.Attributes, new ResolveOpts(iter, false, true));

      var postSpecErrorCount = ErrorCount;

      // Resolve body
      if (iter.Body != null) {
        ResolveBlockStatement(iter.Body, false, iter);
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        CreateIteratorMethodSpecs(iter);
      }
    }

    /// <summary>
    /// Assumes the specification of the iterator itself has been successfully resolved.
    /// </summary>
    void CreateIteratorMethodSpecs(IteratorDecl iter) {
      Contract.Requires(iter != null);

      // ---------- here comes the constructor ----------
      // same requires clause as the iterator itself
      iter.Member_Init.Req.AddRange(iter.Requires);
      // modifies this;
      iter.Member_Init.Mod.Expressions.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));
      var ens = iter.Member_Init.Ens;
      foreach (var p in iter.Ins) {
        // ensures this.x == x;
        ens.Add(new MaybeFreeExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new IdentifierExpr(p.tok, p.Name))));
      }
      foreach (var p in iter.OutsHistoryFields) {
        // ensures this.ys == [];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new SeqDisplayExpr(p.tok, new List<Expression>()))));
      }
      // ensures this.Valid();
      var valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      ens.Add(new MaybeFreeExpression(valid_call));
      // ensures this._reads == old(ReadsClause);
      var modSetSingletons = new List<Expression>();
      Expression frameSet = new SetDisplayExpr(iter.tok, modSetSingletons);
      foreach (var fr in iter.Reads.Expressions) {
        if (fr.FieldName != null) {
          Error(fr.tok, "sorry, a reads clause for an iterator is not allowed to designate specific fields");
        } else if (fr.E.Type.IsRefType) {
          modSetSingletons.Add(fr.E);
        } else {
          frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
        }
      }
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"),
        new OldExpr(iter.tok, frameSet))));
      // ensures this._modifies == old(ModifiesClause);
      modSetSingletons = new List<Expression>();
      frameSet = new SetDisplayExpr(iter.tok, modSetSingletons);
      foreach (var fr in iter.Modifies.Expressions) {
        if (fr.FieldName != null) {
          Error(fr.tok, "sorry, a modifies clause for an iterator is not allowed to designate specific fields");
        } else if (fr.E.Type.IsRefType) {
          modSetSingletons.Add(fr.E);
        } else {
          frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
        }
      }
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"),
        new OldExpr(iter.tok, frameSet))));
      // ensures this._new == {};
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
        new SetDisplayExpr(iter.tok, new List<Expression>()))));
      // ensures this._decreases0 == old(DecreasesClause[0]) && ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), iter.DecreasesFields[i].Name),
          new OldExpr(iter.tok, p))));
      }

      // ---------- here comes predicate Valid() ----------
      var reads = iter.Member_Valid.Reads;
      reads.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));  // reads this;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"), null));  // reads this._reads;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));  // reads this._new;

      // ---------- here comes method MoveNext() ----------
      // requires this.Valid();
      var req = iter.Member_MoveNext.Req;
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      req.Add(new MaybeFreeExpression(valid_call));
      // requires YieldRequires;
      req.AddRange(iter.YieldRequires);
      // modifies this, this._modifies, this._new;
      var mod = iter.Member_MoveNext.Mod.Expressions;
      mod.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));
      // ensures fresh(_new - old(_new));
      ens = iter.Member_MoveNext.Ens;
      ens.Add(new MaybeFreeExpression(new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Fresh,
        new BinaryExpr(iter.tok, BinaryExpr.Opcode.Sub,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
          new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))))));
      // ensures more ==> this.Valid();
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
        new IdentifierExpr(iter.tok, "more"),
        valid_call)));
      // ensures this.ys == if more then old(this.ys) + [this.y] else old(this.ys);
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var ite = new ITEExpr(iter.tok, new IdentifierExpr(iter.tok, "more"),
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add,
            new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)),
            new SeqDisplayExpr(iter.tok, new List<Expression>() { new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), y.Name) })),
          new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)));
        var eq = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name), ite);
        ens.Add(new MaybeFreeExpression(eq));
      }
      // ensures more ==> YieldEnsures;
      foreach (var ye in iter.YieldEnsures) {
        ens.Add(new MaybeFreeExpression(
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp, new IdentifierExpr(iter.tok, "more"), ye.E),
          ye.IsFree));
      }
      // ensures !more ==> Ensures;
      foreach (var e in iter.Ensures) {
        ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
          new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Not, new IdentifierExpr(iter.tok, "more")),
          e.E),
          e.IsFree));
      }
      // decreases this._decreases0, this._decreases1, ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        iter.Member_MoveNext.Decreases.Expressions.Add(new MemberSelectExpr(p.tok, new ThisExpr(p.tok), iter.DecreasesFields[i].Name));
      }
      iter.Member_MoveNext.Decreases.Attributes = iter.Decreases.Attributes;
    }

    // Like the ResolveTypeOptionEnum, but iff the case of AllowPrefixExtend, it also
    // contains a pointer to its Parent class, to fill in default type parameters properly.
    public class ResolveTypeOption
    {
      public readonly ResolveTypeOptionEnum Opt;
      public readonly TypeParameter.ParentType Parent;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant((Opt == ResolveTypeOptionEnum.AllowPrefixExtend) == (Parent != null));
      }

      public ResolveTypeOption(ResolveTypeOptionEnum opt) {
        Contract.Requires(opt != ResolveTypeOptionEnum.AllowPrefixExtend);
        Parent = null;
        Opt = opt;
      }

      public ResolveTypeOption(TypeParameter.ParentType parent) {
        Contract.Requires(parent != null);
        Opt = ResolveTypeOptionEnum.AllowPrefixExtend;
        Parent = parent;
      }
    }

    /// <summary>
    /// If ResolveType/ResolveTypeLenient encounters a (datatype or class) type "C" with no supplied arguments, then
    /// the ResolveTypeOption says what to do.  The last three options take a List as a parameter, which (would have
    /// been supplied as an argument if C# had datatypes instead of just enums, but since C# doesn't) is supplied
    /// as another parameter (called 'defaultTypeArguments') to ResolveType/ResolveTypeLenient.
    /// </summary>
    public enum ResolveTypeOptionEnum
    {
      /// <summary>
      /// never infer type arguments
      /// </summary>
      DontInfer,
      /// <summary>
      /// create a new InferredTypeProxy type for each needed argument
      /// </summary>
      InferTypeProxies,
      /// <summary>
      /// if at most defaultTypeArguments.Count type arguments are needed, use a prefix of defaultTypeArguments
      /// </summary>
      AllowPrefix,
      /// <summary>
      /// same as AllowPrefix, but if more than defaultTypeArguments.Count type arguments are needed, first
      /// extend defaultTypeArguments to a sufficient length
      /// </summary>
      AllowPrefixExtend,
    }

    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// </summary>
    public void ResolveType(IToken tok, Type type, ICodeContext context, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires(eopt != ResolveTypeOptionEnum.AllowPrefixExtend);
      ResolveType(tok, type, context, new ResolveTypeOption(eopt), defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext context, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires(option != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      var r = ResolveTypeLenient(tok, type, context, option, defaultTypeArguments, false);
      Contract.Assert(r == null);
    }

    public class ResolveTypeReturn
    {
      public readonly Type ReplacementType;
      public readonly ExprDotName LastComponent;
      public ResolveTypeReturn(Type replacementType, ExprDotName lastComponent) {
        Contract.Requires(replacementType != null);
        Contract.Requires(lastComponent != null);
        ReplacementType = replacementType;
        LastComponent = lastComponent;
      }
    }
    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// One more thing:  if "allowDanglingDotName" is true, then if the resolution would have produced
    ///   an error message that could have been avoided if "type" denoted an identifier sequence one
    ///   shorter, then return an unresolved replacement type where the identifier sequence is one
    ///   shorter.  (In all other cases, the method returns null.)
    /// </summary>
    public ResolveTypeReturn ResolveTypeLenient(IToken tok, Type type, ICodeContext context, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments, bool allowDanglingDotName) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      if (type is BasicType) {
        // nothing to resolve
      } else if (type is MapType) {
        var mt = (MapType)type;
        var errorCount = ErrorCount;
        int typeArgumentCount = 0;
        if (mt.HasTypeArg()) {
          ResolveType(tok, mt.Domain, context, option, defaultTypeArguments);
          ResolveType(tok, mt.Range, context, option, defaultTypeArguments);
          typeArgumentCount = 2;
        } else if (option.Opt != ResolveTypeOptionEnum.DontInfer) {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 2, inferredTypeArgs, defaultTypeArguments, option);
          Contract.Assert(inferredTypeArgs.Count <= 2);
          if (inferredTypeArgs.Count != 0) {
            mt.SetTypeArg(inferredTypeArgs[0]);
            typeArgumentCount++;
          }
          if (inferredTypeArgs.Count == 2) {
            mt.SetRangetype(inferredTypeArgs[1]);
            typeArgumentCount++;
          }
        }
        // defaults and auto have been applied; check if we now have the right number of arguments
        if (2 != typeArgumentCount) {
          Error(tok, "Wrong number of type arguments ({0} instead of 2) passed to type: {1}", typeArgumentCount, mt.CollectionTypeName);
          // add proxy types, to make sure that MapType will have have a non-null Arg/Domain and Range
          if (typeArgumentCount == 0) {
            mt.SetTypeArg(new InferredTypeProxy());
          }
          mt.SetRangetype(new InferredTypeProxy());
        }
        if (errorCount == ErrorCount && (mt.Domain.IsSubrangeType || mt.Range.IsSubrangeType)) {
          Error(tok, "sorry, cannot instantiate collection type with a subrange type");
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var errorCount = ErrorCount;
        if (t.HasTypeArg()) {
          ResolveType(tok, t.Arg, context, option, defaultTypeArguments);
        } else if (option.Opt != ResolveTypeOptionEnum.DontInfer) {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 1, inferredTypeArgs, defaultTypeArguments, option);
          if (inferredTypeArgs.Count != 0) {
            Contract.Assert(inferredTypeArgs.Count == 1);
            t.SetTypeArg(inferredTypeArgs[0]);
          }
        }
        if (!t.HasTypeArg()) {
          // defaults and auto have been applied; check if we now have the right number of arguments
          Error(tok, "Wrong number of type arguments (0 instead of 1) passed to type: {0}", t.CollectionTypeName);
          // add a proxy type, to make sure that CollectionType will have have a non-null Arg
          t.SetTypeArg(new InferredTypeProxy());
        }

        if (errorCount == ErrorCount && t.Arg.IsSubrangeType) {
          Error(tok, "sorry, cannot instantiate collection type with a subrange type");
        }

      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass != null || t.ResolvedParam != null) {
          // Apparently, this type has already been resolved
          return null;
        }
        var prevErrorCount = ErrorCount;
        if (t.NamePath is ExprDotName) {
          var ret = ResolveDotSuffix_Type((ExprDotName)t.NamePath, new ResolveOpts(context, true, true), allowDanglingDotName, option, defaultTypeArguments);
          if (ret != null) {
            return ret;
          }
        } else {
          var s = (NameSegment)t.NamePath;
          ResolveNameSegment_Type(s, new ResolveOpts(context, true, true), option, defaultTypeArguments);
        }
        if (ErrorCount == prevErrorCount) {
          var r = t.NamePath.Resolved as Resolver_IdentifierExpr;
          if (r == null || !(r.Type is Resolver_IdentifierExpr.ResolverType_Type)) {
            Error(t.tok, "expected type");
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type && r.TypeParamDecl != null) {
            t.ResolvedParam = r.TypeParamDecl;
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var d = r.Decl;
            if (d is OpaqueTypeDecl) {
              t.ResolvedParam = ((OpaqueTypeDecl)d).TheType;  // resolve like a type parameter, and it may have type parameters if it's an opaque type
            } else if (d is NewtypeDecl) {
              var dd = (NewtypeDecl)d;
              var caller = context as ICallable;
              if (caller != null) {
                caller.EnclosingModule.CallGraph.AddEdge(caller, dd);
                if (caller == dd) {
                  // detect self-loops here, since they don't show up in the graph's SSC methods
                  Error(dd.tok, "recursive dependency involving a newtype: {0} -> {0}", dd.Name);
                }
              }
              t.ResolvedClass = dd;
            } else {
              // d is a class or datatype, and it may have type parameters
              t.ResolvedClass = d;
            }
            if (option.Opt == ResolveTypeOptionEnum.DontInfer) {
              // don't add anything
            } else if (d.TypeArgs.Count != t.TypeArgs.Count && t.TypeArgs.Count == 0) {
              FillInTypeArguments(t.tok, d.TypeArgs.Count, t.TypeArgs, defaultTypeArguments, option);
            }
            // defaults and auto have been applied; check if we now have the right number of arguments
            if (d.TypeArgs.Count != t.TypeArgs.Count) {
              Error(t.tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", t.TypeArgs.Count, d.TypeArgs.Count, d.WhatKind, t.Name);
            }

          }
        }

      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(tok, t.T, context, option, defaultTypeArguments);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return null;
    }

    bool ReallyAmbiguousTopLevelDecl(ref TopLevelDecl decl) {
      return ReallyAmbiguousThing(ref decl, (d0, d1) => {
        // We'd like to resolve any AliasModuleDecl to whatever module they refer to.
        // It seems that the only way to do that is to look at alias.Signature.ModuleDef,
        // but that is a ModuleDefinition, which is not a TopLevelDecl.  Therefore, we
        // convert to a ModuleDefinition anything that might refer to something that an
        // AliasModuleDecl can refer to; this is AliasModuleDecl and LiteralModuleDecl.
        object a = d0 is ModuleDecl ? ((ModuleDecl)d0).Dereference() : d0;
        object b = d1 is ModuleDecl ? ((ModuleDecl)d1).Dereference() : d1;
        return a == b;
      });
    }

    bool ReallyAmbiguousThing<Thing>(ref Thing decl, Func<Thing, Thing, bool> eq = null) where Thing : class {
      Contract.Requires(decl != null);
      Contract.Ensures(decl != null);
      Contract.Ensures(!Contract.Result<bool>() || (decl == Contract.OldValue<Thing>(decl) && decl is IAmbiguousThing<Thing>));
      var amb = decl as IAmbiguousThing<Thing>;
      if (amb != null) {
        var allDecls = new List<Thing>(amb.AllDecls());
        Contract.Assert(1 <= allDecls.Count);  // that's what the specification of AllDecls says
        var repr = allDecls[0];  // pick one of them
        // check if all are the same
        if (amb.AllDecls().All(d => eq == null ? d == repr : eq(d, repr))) {
          // all ambiguity gets resolved to the same declaration, so there really isn't any ambiguity after all
          decl = repr;
          return false;
        }
        return true;  // decl is an AmbiguousThing and the declarations it can stand for are not all the same--so this really is an ambiguity
      }
      return false;
    }

    /// <summary>
    /// Adds to "typeArgs" a list of "n" type arguments, possibly extending "defaultTypeArguments".
    /// </summary>
    static void FillInTypeArguments(IToken tok, int n, List<Type> typeArgs, List<TypeParameter> defaultTypeArguments, ResolveTypeOption option) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      Contract.Requires(typeArgs != null && typeArgs.Count == 0);
      if (option.Opt == ResolveTypeOptionEnum.InferTypeProxies) {
        // add type arguments that will be inferred
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new InferredTypeProxy());
        }
      } else if (option.Opt == ResolveTypeOptionEnum.AllowPrefix && defaultTypeArguments.Count < n) {
        // there aren't enough default arguments, so don't do anything
      } else {
        // we'll add arguments
        if (option.Opt == ResolveTypeOptionEnum.AllowPrefixExtend) {
          // extend defaultTypeArguments, if needed
          for (int i = defaultTypeArguments.Count; i < n; i++) {
            var tp = new TypeParameter(tok, "_T" + i, i, option.Parent);
            defaultTypeArguments.Add(tp);
          }
        }
        Contract.Assert(n <= defaultTypeArguments.Count);
        // automatically supply a prefix of the arguments from defaultTypeArguments
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new UserDefinedType(defaultTypeArguments[i]));
        }
      }
    }

    public bool UnifyTypes(Type a, Type b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);

      a = a.NormalizeExpand();
      b = b.NormalizeExpand();
      if (a is TypeProxy) {
        // merge a and b (cycles are avoided even if b is a TypeProxy, since we have got to the bottom of both a and b)
        return AssignProxy((TypeProxy)a, b);
      } else if (b is TypeProxy) {
        // merge a and b
        return AssignProxy((TypeProxy)b, a);
      }

#if !NO_CHEAP_OBJECT_WORKAROUND
      if (a is ObjectType || b is ObjectType) {  // TODO: remove this temporary hack
        var other = a is ObjectType ? b : a;
        if (!other.IsRefType) {
          return false;
        }
        // allow anything else with object; this is BOGUS
        return true;
      }
#endif
      // Now, a and b are non-proxies and stand for the same things as the original a and b, respectively.

      if (a is BoolType) {
        return b is BoolType;
      } else if (a is CharType) {
        return b is CharType;
      } else if (a is IntType) {
        return b is IntType;
      } else if (a is RealType) {
        return b is RealType;
      } else if (a is ObjectType) {
        return b is ObjectType;
      } else if (a is SetType) {
        return b is SetType && UnifyTypes(((SetType)a).Arg, ((SetType)b).Arg);
      } else if (a is MultiSetType) {
        return b is MultiSetType && UnifyTypes(((MultiSetType)a).Arg, ((MultiSetType)b).Arg);
      } else if (a is MapType) {
        return b is MapType && ((MapType)a).Finite == ((MapType)b).Finite &&
               UnifyTypes(((MapType)a).Domain, ((MapType)b).Domain) && UnifyTypes(((MapType)a).Range, ((MapType)b).Range);
      } else if (a is SeqType) {
        return b is SeqType && UnifyTypes(((SeqType)a).Arg, ((SeqType)b).Arg);
      } else if (a is UserDefinedType) {
        if (!(b is UserDefinedType)) {
          return false;
        }
        var aa = (UserDefinedType)a;
        var bb = (UserDefinedType)b;
        if (aa.ResolvedClass != null && aa.ResolvedClass == bb.ResolvedClass) {
          // these are both resolved class/datatype types
          Contract.Assert(aa.TypeArgs.Count == bb.TypeArgs.Count);
          bool successSoFar = true;
          for (int i = 0; successSoFar && i < aa.TypeArgs.Count; i++) {
            successSoFar = UnifyTypes(aa.TypeArgs[i], bb.TypeArgs[i]);
          }
          return successSoFar;
        }
        else if ((bb.ResolvedClass is TraitDecl) && (aa.ResolvedClass is TraitDecl)) {
            return ((TraitDecl)bb.ResolvedClass).FullCompileName == ((TraitDecl)aa.ResolvedClass).FullCompileName;
        } else if ((bb.ResolvedClass is ClassDecl) && (aa.ResolvedClass is TraitDecl)) {
            return ((ClassDecl)bb.ResolvedClass).TraitsObj.Any(tr => tr.FullCompileName == ((TraitDecl)aa.ResolvedClass).FullCompileName);
        } else if ((aa.ResolvedClass is ClassDecl) && (bb.ResolvedClass is TraitDecl)) {
            return ((ClassDecl)aa.ResolvedClass).TraitsObj.Any(tr => tr.FullCompileName == ((TraitDecl)bb.ResolvedClass).FullCompileName);
        } else if (aa.ResolvedParam != null && aa.ResolvedParam == bb.ResolvedParam) {
          // type parameters
          if (aa.TypeArgs.Count != bb.TypeArgs.Count) {
            return false;
          } else {
            bool successSoFar = true;
            for (int i = 0; i < aa.TypeArgs.Count; i++) {
              if (!UnifyTypes(aa.TypeArgs[i], bb.TypeArgs[i])) {
                successSoFar = false;
              }
            }
            return successSoFar;
          }
        } else {
          // something is wrong; either aa or bb wasn't properly resolved, or they don't unify
          return false;
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    bool AssignProxy(TypeProxy proxy, Type t) {
      Contract.Requires(proxy != null);
      Contract.Requires(t != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
      //modifies proxy.T, ((TypeProxy)t).T;  // might also change t.T if t is a proxy
      Contract.Ensures(Contract.Result<bool>() == (proxy == t || proxy.T != null || (t is TypeProxy && ((TypeProxy)t).T != null)));
      if (proxy == t) {
        // they are already in the same equivalence class
        return true;

      } else if (proxy is UnrestrictedTypeProxy) {
        // it's fine to redirect proxy to t (done below)

      } else if (t is UnrestrictedTypeProxy) {
        // merge proxy and t by redirecting t to proxy, rather than the other way around
        ((TypeProxy)t).T = proxy;
        return true;

      } else if (t is RestrictedTypeProxy) {
        // Both proxy and t are restricted type proxies.  To simplify unification, order proxy and t
        // according to their types.
        RestrictedTypeProxy r0 = (RestrictedTypeProxy)proxy;
        RestrictedTypeProxy r1 = (RestrictedTypeProxy)t;
        if (r0.OrderID <= r1.OrderID) {
          return AssignRestrictedProxies(r0, r1);
        } else {
          return AssignRestrictedProxies(r1, r0);
        }

        // In the remaining cases, proxy is a restricted proxy and t is a non-proxy
      } else if (proxy is DatatypeProxy) {
        var dtp = (DatatypeProxy)proxy;
        if (!dtp.Co && t.NormalizeExpand().IsIndDatatype) {
          // all is fine, proxy can be redirected to t
        } else if (dtp.Co && t.IsCoDatatype) {
          // all is fine, proxy can be redirected to t
        } else if (dtp.TypeVariableOK && t.IsTypeParameter) {
          // looking good
        } else {
          return false;
        }

      } else if (proxy is ObjectTypeProxy) {
        if (t is ArrowType) {
          return false;
        } else if (t is ObjectType || UserDefinedType.DenotesClass(t) != null) {
          // all is fine, proxy can be redirected to t
        } else {
          return false;
        }

      } else if (proxy is CollectionTypeProxy) {
        CollectionTypeProxy collProxy = (CollectionTypeProxy)proxy;
        if (t is CollectionType) {
          if (!UnifyTypes(collProxy.Arg, ((CollectionType)t).Arg)) {
            return false;
          }
        } else {
          return false;
        }

      } else if (proxy is OperationTypeProxy) {
        var opProxy = (OperationTypeProxy)proxy;
        if (opProxy.AllowInts && t.IsNumericBased(Type.NumericPersuation.Int)) {
          // fine
        } else if (opProxy.AllowReals && t.IsNumericBased(Type.NumericPersuation.Real)) {
          // fine
        } else if (opProxy.AllowChar && t is CharType) {
          // fine
        } else if (opProxy.AllowSetVarieties && (t is SetType || t is MultiSetType)) {
          // fine
        } else if (opProxy.AllowSeq && t is SeqType) {
          // fine
        } else {
          return false;
        }

      } else if (proxy is IndexableTypeProxy) {
        var iProxy = (IndexableTypeProxy)proxy;
        if (t is SeqType) {
          if (!UnifyTypes(iProxy.Domain, new OperationTypeProxy(true, false, false, false, false))) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, ((SeqType)t).Arg)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Range)) {
            return false;
          }
        } else if (iProxy.AllowArray && t.IsArrayType && t.AsArrayType.Dims == 1) {
          Type elType = UserDefinedType.ArrayElementType(t);
          if (!UnifyTypes(iProxy.Domain, new OperationTypeProxy(true, false, false, false, false))) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, elType)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Range)) {
            return false;
          }
        } else if (iProxy.AllowMap && t is MapType && ((MapType)t).Finite) {
          if (!UnifyTypes(iProxy.Domain, ((MapType)t).Domain)) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, ((MapType)t).Range)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Domain)) {
            return false;
          }
        } else if (iProxy.AllowIMap && t is MapType && !((MapType)t).Finite) {
          if (!UnifyTypes(iProxy.Domain, ((MapType)t).Domain)) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, ((MapType)t).Range)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Domain)) {
            return false;
          }
        } else if (t is MultiSetType) {
          if (!UnifyTypes(iProxy.Domain, ((MultiSetType)t).Arg)) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, new OperationTypeProxy(true, false, false, false, false))) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Domain)) {
            return false;
          }
        } else {
          return false;
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected proxy type
      }

      // do the merge, but never infer a subrange type
      if (t is NatType) {
        proxy.T = Type.Int;
      } else {
        return AssignProxyAfterCycleCheck(proxy, t);
      }
      return true;
    }

    bool AssignProxyAfterCycleCheck(TypeProxy proxy, Type t) {
      Contract.Requires(proxy != null && proxy.T == null);
      Contract.Requires(t != null);
      if (TypeArgumentsIncludeProxy(t, proxy)) {
        return false;
      } else {
        proxy.T = t;
        return true;
      }
    }

    bool TypeArgumentsIncludeProxy(Type t, TypeProxy proxy) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      foreach (var ta in t.TypeArgs) {
        var a = ta.Normalize();
        if (a == proxy || TypeArgumentsIncludeProxy(a, proxy)) {
          return true;
        }
      }
      return false;
    }

    bool AssignRestrictedProxies(RestrictedTypeProxy a, RestrictedTypeProxy b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a != b);
      Contract.Requires(a.T == null && b.T == null);
      Contract.Requires(a.OrderID <= b.OrderID);
      //modifies a.T, b.T;
      Contract.Ensures(!Contract.Result<bool>() || a.T != null || b.T != null);

      if (a is DatatypeProxy) {
        if (b is DatatypeProxy && ((DatatypeProxy)a).Co == ((DatatypeProxy)b).Co) {
          // all is fine
          a.T = b;
          return true;
        } else {
          return false;
        }
      } else if (a is ObjectTypeProxy) {
        if (b is ObjectTypeProxy) {
          // all is fine
          a.T = b;
          return true;
        } else if (b is IndexableTypeProxy && ((IndexableTypeProxy)b).AllowArray) {
          var ib = (IndexableTypeProxy)b;
          // the intersection of ObjectTypeProxy and IndexableTypeProxy is an array type
          // Note, we're calling ResolvedArrayType here, which in turn calls ResolveType on ib.Arg.  However, we
          // don't need to worry about what ICodeContext we're passing in, because ib.Arg should already have been
          // resolved.
          var c = ResolvedArrayType(Token.NoToken, 1, ib.Arg, new DontUseICallable());
          return AssignProxyAfterCycleCheck(a, c) && AssignProxyAfterCycleCheck(b, c) && UnifyTypes(ib.Arg, ib.Range);
        } else {
          return false;
        }

      } else if (a is CollectionTypeProxy) {
        if (b is CollectionTypeProxy) {
          a.T = b;
          return UnifyTypes(((CollectionTypeProxy)a).Arg, ((CollectionTypeProxy)b).Arg);
        } else if (b is OperationTypeProxy) {
          var proxy = (OperationTypeProxy)b;
          if (proxy.AllowSeq && proxy.AllowSetVarieties) {
            b.T = a;  // a is a stronger constraint than b
          } else {
            // a says set<T>,seq<T> and b says numeric,set; the intersection is set<T>
            var c = new SetType(((CollectionTypeProxy)a).Arg);
            return AssignProxyAfterCycleCheck(a, c) && AssignProxyAfterCycleCheck(b, c);
          }
          return true;
        } else if (b is IndexableTypeProxy) {
          var pa = (CollectionTypeProxy)a;
          var ib = (IndexableTypeProxy)b;
          // pa is:
          //   set(Arg) or multiset(Arg) or seq(Arg) or map(Arg, anyRange) or imap(Arg, anyRange)
          // ib is:
          //   multiset(Arg) or
          //   seq(Arg) or
          //   if AllowMap, map(Domain, Arg), or
          //   if AllowIMap, imap(Domain, Arg), or
          //   if AllowArray, array(Arg)
          // Their intersection is:
          if (ib.AllowArray) {
            var c = new IndexableTypeProxy(ib.Domain, ib.Range, ib.Arg, ib.AllowMap, ib.AllowIMap, false);
            ib.T = c;
            ib = c;
          }
          pa.T = ib;
          return UnifyTypes(pa.Arg, ib.Arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
        }

      } else if (a is OperationTypeProxy) {
        var pa = (OperationTypeProxy)a;
        if (b is OperationTypeProxy) {
          var pb = (OperationTypeProxy)b;
          var i = pa.AllowInts && pb.AllowInts;
          var r = pa.AllowReals && pb.AllowReals;
          var h = pa.AllowChar && pb.AllowChar;
          var q = pa.AllowSeq && pb.AllowSeq;
          var s = pa.AllowSetVarieties && pb.AllowSetVarieties;
          if (!i && !r && !h && !q && !s) {
            // over-constrained
            return false;
          } else if (i == pa.AllowInts && r == pa.AllowReals && h == pa.AllowChar && q == pa.AllowSeq && s == pa.AllowSetVarieties) {
            b.T = a;  // a has the stronger requirement
          } else if (i == pb.AllowInts && r == pb.AllowReals && h == pb.AllowChar && q == pb.AllowSeq && s == pb.AllowSetVarieties) {
            a.T = b;  // b has the stronger requirement
          } else {
            Type c = !i && !r && h && !q && !s ? new CharType() : (Type)new OperationTypeProxy(i, r, h, q, s);
            // the calls to AssignProxyAfterCycleCheck are needed only when c is a non-proxy type, but it doesn't
            // hurt to do them in both cases
            return AssignProxyAfterCycleCheck(a, c) && AssignProxyAfterCycleCheck(b, c);
          }
          return true;
        } else {
          var ib = (IndexableTypeProxy)b;  // cast justification:  else we have unexpected restricted-proxy type
          // a is:  possibly numeric, possibly char, possibly seq, possibly set or multiset
          // b is:  seq, multiset, possibly map, possibly array -- with some constraints about the type parameterization
          // So, the intersection could include multiset and seq.
          if (pa.AllowSetVarieties && !pa.AllowSeq) {
            // strengthen a and b to a multiset type
            var c = new MultiSetType(ib.Arg);
            return AssignProxyAfterCycleCheck(a, c) && AssignProxyAfterCycleCheck(b, c);
          } else if (pa.AllowSeq && !pa.AllowSetVarieties) {
            // strengthen a and b to a sequence type
            var c = new SeqType(ib.Arg);
            return AssignProxyAfterCycleCheck(a, c) && AssignProxyAfterCycleCheck(b, c);
          } else if (!pa.AllowSeq && !pa.AllowSetVarieties) {
            // over-constrained
            return false;
          } else {
            Contract.Assert(pa.AllowSeq && pa.AllowSetVarieties);  // the only case left
            if (ib.AllowMap || ib.AllowIMap || ib.AllowArray) {
              var c = new IndexableTypeProxy(ib.Domain, ib.Range, ib.Arg, false, false, false);
              a.T = c;
              b.T = c;
            } else {
              a.T = b;
            }
            return true;
          }
        }

      } else if (a is IndexableTypeProxy) {
        var ia = (IndexableTypeProxy)a;
        var ib = (IndexableTypeProxy)b;  // cast justification: else we have unexpected restricted-proxy type
        var am = ia.AllowMap && ib.AllowMap;
        var aim = ia.AllowIMap && ib.AllowIMap;
        var ar = ia.AllowArray && ib.AllowArray;
        if (am == ia.AllowMap && aim == ia.AllowIMap && ar == ia.AllowArray) {
          b.T = a;  // a has the stronger requirement
        } else if (am == ib.AllowMap && aim == ib.AllowIMap && ar == ib.AllowArray) {
          a.T = b;  // b has the stronger requirement
        } else {
          var c = new IndexableTypeProxy(ia.Domain, ia.Range, ia.Arg, am, aim, ar);
          a.T = c;
          b.T = c;
        }
        return UnifyTypes(ia.Domain, ib.Domain) && UnifyTypes(ia.Range, ib.Range) && UnifyTypes(ia.Arg, ib.Arg);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
      }
    }

    /// <summary>
    /// Returns a resolved type denoting an array type with dimension "dims" and element type "arg".
    /// Callers are expected to provide "arg" as an already resolved type.  (Note, a proxy type is resolved--
    /// only types that contain identifiers stand the possibility of not being resolved.)
    /// </summary>
    Type ResolvedArrayType(IToken tok, int dims, Type arg, ICodeContext context) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      var at = builtIns.ArrayType(tok, dims, new List<Type> { arg }, false);
      ResolveType(tok, at, context, ResolveTypeOptionEnum.DontInfer, null);
      return at;
    }

    /// <summary>
    /// "specContextOnly" means that the statement must be erasable, that is, it should be okay to omit it
    /// at run time.  That means it must not have any side effects on non-ghost variables, for example.
    /// </summary>
    public void ResolveStatement(Statement stmt, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      if (!(stmt is ForallStmt)) {  // forall statements do their own attribute resolution below
        ResolveAttributes(stmt.Attributes, new ResolveOpts(codeContext, true, true));
      }
      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        s.IsGhost = true;
        ResolveExpression(s.Expr, new ResolveOpts(codeContext, true, true));
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Expr.Type, Type.Bool)) {
          Error(s.Expr, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Expr.Type);
        }

      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        ResolveAttributeArgs(s.Args, new ResolveOpts(codeContext, false, specContextOnly), false);
        if (specContextOnly) {
          Error(stmt, "print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
        }

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = labeledStatements.Find(s.TargetLabel);
          if (target == null) {
            Error(s, "break label is undefined or not in scope: {0}", s.TargetLabel);
          } else {
            s.TargetStmt = target;
            bool targetIsLoop = target is WhileStmt || target is AlternativeLoopStmt;
            if (specContextOnly && !s.TargetStmt.IsGhost && !inSpecOnlyContext[s.TargetStmt]) {
              Error(stmt, "ghost-context break statement is not allowed to break out of non-ghost " + (targetIsLoop ? "loop" : "structure"));
            }
          }
        } else {
          if (loopStack.Count < s.BreakCount) {
            Error(s, "trying to break out of more loop levels than there are enclosing loops");
          } else {
            Statement target = loopStack[loopStack.Count - s.BreakCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
            if (specContextOnly && !target.IsGhost && !inSpecOnlyContext[target]) {
              Error(stmt, "ghost-context break statement is not allowed to break out of non-ghost loop");
            }
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(codeContext is IteratorDecl)) {
          Error(stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(codeContext is Method)) {
          Error(stmt, "return statement is allowed only in method");
        } else if (specContextOnly && !codeContext.IsGhost) {
          Error(stmt, "{0} statement is not allowed in this context (because it is guarded by a specification-only expression)", kind);
        }
        var s = (ProduceStmt)stmt;
        if (s.rhss != null) {
          var cmc = codeContext as IMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.rhss.Count) {
            Error(s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new IdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                ident.Var = f;
                ident.Type = ident.Var.Type;
                Contract.Assert(f.Type != null);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, new ResolveOpts(codeContext, true));
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.hiddenUpdate = new UpdateStmt(s.Tok, s.EndTok, formals, s.rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.hiddenUpdate, specContextOnly, codeContext);
          }
        } else {// this is a regular return/yield statement.
          s.hiddenUpdate = null;
        }
      } else if (stmt is ConcreteUpdateStatement) {
        ResolveConcreteUpdateStmt((ConcreteUpdateStatement)stmt, specContextOnly, codeContext);
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have three cases.
        Contract.Assert(s.Update == null || s.Update is UpdateStmt || s.Update is AssignSuchThatStmt);
        // 0.  There is no .Update.  This is easy, we will just resolve the locals.
        // 1.  The .Update is an AssignSuchThatStmt.  This is also straightforward:  first
        //     resolve the locals, which adds them to the scope, and then resolve the .Update.
        // 2.  The .Update is an UpdateStmt, which, resolved, means either a CallStmt or a bunch
        //     of parallel AssignStmt's.  Here, the right-hand sides should be resolved before
        //     the local variables have been added to the scope, but the left-hand sides should
        //     resolve to the newly introduced variables.
        // To accommodate these options, we first reach into the UpdateStmt, if any, to resolve
        // the left-hand sides of the UpdateStmt.  This will have the effect of shielding them
        // from a subsequent resolution (since expression resolution will do nothing if the .Type
        // field is already assigned.
        // Alright, so it is:

        // Resolve the types of the locals
        foreach (var local in s.Locals) {
          ResolveType(local.Tok, local.OptionalType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          local.type = local.OptionalType;
          if (specContextOnly) {
            // a local variable in a specification-only context might as well be ghost
            local.IsGhost = true;
          }
        }
        // Resolve the UpdateStmt, if any
        if (s.Update is UpdateStmt) {
          var upd = (UpdateStmt)s.Update;
          // resolve the LHS
          Contract.Assert(upd.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < upd.Lhss.Count; i++) {
            var local = s.Locals[i];
            var lhs = (IdentifierExpr)upd.Lhss[i];  // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
            Contract.Assert(lhs.Type == null);  // not yet resolved
            lhs.Var = local;
            lhs.Type = local.Type;
          }
          // resolve the whole thing
          ResolveConcreteUpdateStmt(s.Update, specContextOnly, codeContext);
        }
        // Add the locals to the scope
        foreach (var local in s.Locals) {
          if (!scope.Push(local.Name, local)) {
            Error(local.Tok, "Duplicate local-variable name: {0}", local.Name);
          }
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in s.Locals) {
          ResolveAttributes(local.Attributes, new ResolveOpts(codeContext, true, true));
        }
        // Resolve the AssignSuchThatStmt, if any
        if (s.Update is AssignSuchThatStmt) {
          ResolveConcreteUpdateStmt(s.Update, specContextOnly, codeContext);
        }
        // Update the VarDeclStmt's ghost status according to its components
        if (!s.IsGhost) {
          s.IsGhost = (s.Update == null || s.Update.IsGhost) && s.Locals.All(v => v.IsGhost);
        }
        foreach (var local in s.Locals)
        {
          if (Attributes.Contains(local.Attributes, "assumption"))
          {
            if (currentMethod == null)
            {
              Error(local.Tok, "assumption variable can only be declared in a method");
            }
            if (!local.IsGhost)
            {
              Error(local.Tok, "assumption variable must be ghost");
            }
            if (!(local.Type.IsBoolType))
            {
              Error(s, "assumption variable must be of type 'bool'");
            }
          }
        }

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Lhs, new ResolveOpts(codeContext, true, specContextOnly));  // allow ghosts for now, tighted up below
        bool lhsResolvedSuccessfully = ErrorCount == prevErrorCount;
        Contract.Assert(s.Lhs.Type != null);  // follows from postcondition of ResolveExpression
        // check that LHS denotes a mutable variable or a field
        bool lvalueIsGhost = false;
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            lvalueIsGhost = var.IsGhost || codeContext.IsGhost;
            CheckIsLvalue(lhs, codeContext);
            if (!lvalueIsGhost && specContextOnly) {
              Error(stmt, "Assignment to non-ghost variable is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
            }

            var localVar = var as LocalVariable;
            if (localVar != null && currentMethod != null && Attributes.Contains(localVar.Attributes, "assumption"))
            {
              var rhs = s.Rhs as ExprRhs;
              var expr = (rhs != null ? rhs.Expr : null);
              var binaryExpr = expr as BinaryExpr;
              if (binaryExpr != null
                  && (binaryExpr.Op == BinaryExpr.Opcode.And)
                  && (binaryExpr.E0.Resolved is IdentifierExpr)
                  && ((IdentifierExpr)(binaryExpr.E0.Resolved)).Var == localVar
                  && !currentMethod.AssignedAssumptionVariables.Contains(localVar))
              {
                currentMethod.AssignedAssumptionVariables.Add(localVar);
              }
              else
              {
                Error(stmt, string.Format("there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{0} && <boolean expression>\"", localVar.Name));
              }
            }
          }
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          if (fse.Member != null) {  // otherwise, an error was reported above
            lvalueIsGhost = fse.Member.IsGhost;
            if (!lvalueIsGhost) {
              if (specContextOnly) {
                Error(stmt, "Assignment to non-ghost field is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
              } else {
                // It is now that we wish we would have resolved s.Lhs to not allow ghosts.  Too late, so we do
                // the next best thing.
                if (lhsResolvedSuccessfully && UsesSpecFeatures(fse.Obj)) {
                  Error(stmt, "Assignment to non-ghost field is not allowed to use specification-only expressions in the receiver");
                }
              }
            }
            CheckIsLvalue(fse, codeContext);
          }
        } else if (lhs is SeqSelectExpr) {
          var slhs = (SeqSelectExpr)lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(slhs.Seq.Type != null);
            if (specContextOnly) {
              Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
            }
            CheckIsLvalue(slhs, codeContext);
          }

        } else if (lhs is MultiSelectExpr) {
          if (specContextOnly) {
            Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          }
          CheckIsLvalue(lhs, codeContext);

        } else {
          CheckIsLvalue(lhs, codeContext);
        }

        s.IsGhost = lvalueIsGhost;
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, new ResolveOpts(codeContext, true, specContextOnly));
          if (!lvalueIsGhost) {
            CheckIsNonGhost(rr.Expr);
          }
          Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(lhsType, rr.Expr.Type)) {
            Error(stmt, "RHS (of type {0}) not assignable to LHS (of type {1})", rr.Expr.Type, lhsType);
          }
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          Type t = ResolveTypeRhs(rr, stmt, lvalueIsGhost, codeContext);
          if (!lvalueIsGhost) {
            if (rr.ArrayDimensions != null) {
              foreach (var dim in rr.ArrayDimensions) {
                CheckIsNonGhost(dim);
              }
            }
            if (rr.InitCall != null) {
              foreach (var arg in rr.InitCall.Args) {
                CheckIsNonGhost(arg);
              }
            }
          }
          if (!UnifyTypes(lhsType, t)) {
            Error(stmt, "type {0} is not assignable to LHS (of type {1})", t, lhsType);
          }
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        ResolveCallStmt(s, specContextOnly, codeContext, null);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        ResolveBlockStatement(s, specContextOnly, codeContext);
        if (!s.IsGhost) {
          s.IsGhost = s.Body.All(ss => ss.IsGhost);  // mark the block statement as ghost if all its substatements are ghost
        }
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        bool branchesAreSpecOnly = specContextOnly;
        if (s.Guard != null) {
          int prevErrorCount = ErrorCount;
          ResolveExpression(s.Guard, new ResolveOpts(codeContext, true, specContextOnly));
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          bool successfullyResolved = ErrorCount == prevErrorCount;
          if (!UnifyTypes(s.Guard.Type, Type.Bool)) {
            Error(s.Guard, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Guard.Type);
          }
          if (!specContextOnly && successfullyResolved) {
            branchesAreSpecOnly = UsesSpecFeatures(s.Guard);
          }
        }
        s.IsGhost = branchesAreSpecOnly;
        ResolveStatement(s.Thn, branchesAreSpecOnly, codeContext);
        if (s.Els != null) {
          ResolveStatement(s.Els, branchesAreSpecOnly, codeContext);
        }
        if (!s.IsGhost && s.Thn.IsGhost && (s.Els == null || s.Els.IsGhost)) {
          // mark the entire 'if' statement as ghost if its branches are ghost
          s.IsGhost = true;
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        s.IsGhost = ResolveAlternatives(s.Alternatives, specContextOnly, null, codeContext);
        if (!s.IsGhost) {
          s.IsGhost = s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost));
        }

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        bool bodyMustBeSpecOnly = specContextOnly;
        var fvs = new HashSet<IVariable>();
        bool usesHeap = false, usesOldHeap = false;
        Type usesThis = null;
        if (s.Guard != null) {
          int prevErrorCount = ErrorCount;
          ResolveExpression(s.Guard, new ResolveOpts(codeContext, true, specContextOnly));
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          bool successfullyResolved = ErrorCount == prevErrorCount;
          Translator.ComputeFreeVariables(s.Guard, fvs, ref usesHeap, ref usesOldHeap, ref usesThis, false);
          if (!UnifyTypes(s.Guard.Type, Type.Bool)) {
            Error(s.Guard, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Guard.Type);
          }
          if (!specContextOnly && successfullyResolved) {
            bodyMustBeSpecOnly = UsesSpecFeatures(s.Guard);
          }
        }

        foreach (MaybeFreeExpression inv in s.Invariants) {
          ResolveAttributes(inv.Attributes, new ResolveOpts(codeContext, true, true));
          ResolveExpression(inv.E, new ResolveOpts(codeContext, true, true));
          Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
          Translator.ComputeFreeVariables(inv.E, fvs, ref usesHeap, ref usesOldHeap, ref usesThis, false);
          if (!UnifyTypes(inv.E.Type, Type.Bool)) {
            Error(inv.E, "invariant is expected to be of type {0}, but is {1}", Type.Bool, inv.E.Type);
          }
        }

        ResolveAttributes(s.Decreases.Attributes, new ResolveOpts(codeContext, true, true));
        foreach (Expression e in s.Decreases.Expressions) {
          ResolveExpression(e, new ResolveOpts(codeContext, true, true));
          if (e is WildcardExpr) {
            if (bodyMustBeSpecOnly) {
              Error(e, "'decreases *' is not allowed on ghost loops");
            } else if (!codeContext.AllowsNontermination && !DafnyOptions.O.Dafnycc) {
              Error(e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
            }
          }
          // any type is fine
        }

        if (s.Mod.Expressions != null) {
          ResolveAttributes(s.Mod.Attributes, new ResolveOpts(codeContext, true, true));
          foreach (FrameExpression fe in s.Mod.Expressions) {
            ResolveFrameExpression(fe, false, bodyMustBeSpecOnly, codeContext);
            Translator.ComputeFreeVariables(fe.E, fvs, ref usesHeap, ref usesOldHeap, ref usesThis, false);
          }
        }
        s.IsGhost = s.Body == null || bodyMustBeSpecOnly;
        if (s.Body != null) {
          loopStack.Add(s);  // push
          if (s.Labels == null) {  // otherwise, "s" is already in "inSpecOnlyContext" map
            inSpecOnlyContext.Add(s, specContextOnly);
          }

          ResolveStatement(s.Body, bodyMustBeSpecOnly, codeContext);
          loopStack.RemoveAt(loopStack.Count - 1);  // pop
        } else {
          string text = "havoc {";
          if (fvs.Count != 0) {
            string sep = "";
            foreach (var fv in fvs) {
              text += sep + fv.Name;
              sep = ", ";
            }
          }
          text += "};";  // always terminate with a semi-colon
          ReportAdditionalInformation(s.Tok, text, s.Tok.val.Length);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        s.IsGhost = ResolveAlternatives(s.Alternatives, specContextOnly, s, codeContext);
        foreach (MaybeFreeExpression inv in s.Invariants) {
          ResolveExpression(inv.E, new ResolveOpts(codeContext, true, true));
          Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(inv.E.Type, Type.Bool)) {
            Error(inv.E, "invariant is expected to be of type {0}, but is {1}", Type.Bool, inv.E.Type);
          }
        }

        foreach (Expression e in s.Decreases.Expressions) {
          ResolveExpression(e, new ResolveOpts(codeContext, true, true));
          if (e is WildcardExpr) {
            if (s.IsGhost) {
              Error(e, "'decreases *' is not allowed on ghost loops");
            } else if (!codeContext.AllowsNontermination && !DafnyOptions.O.Dafnycc) {
              Error(e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
            }
          }
          // any type is fine
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.tok, v.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, new ResolveOpts(codeContext, true, specContextOnly));
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Range.Type, Type.Bool)) {
          Error(stmt, "range restriction in forall statement must be of type bool (instead got {0})", s.Range.Type);
        }
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, new ResolveOpts(codeContext, true, true));
          Contract.Assert(ens.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(ens.E.Type, Type.Bool)) {
            Error(ens.E, "ensures condition is expected to be of type {0}, but is {1}", Type.Bool, ens.E.Type);
          }
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s.Attributes, new ResolveOpts(codeContext, true, true));

        bool bodyMustBeSpecOnly = specContextOnly || (prevErrorCount == ErrorCount && UsesSpecFeatures(s.Range));
        if (!bodyMustBeSpecOnly && prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(s.Range);  // we need to resolve operators before the call to DiscoverBounds
          s.Bounds = DiscoverBounds(s.Tok, s.BoundVars, s.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            bodyMustBeSpecOnly = true;
          }
        }
        s.IsGhost = s.Body == null || bodyMustBeSpecOnly;

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = labeledStatements;
          var prevLoopStack = loopStack;
          labeledStatements = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, bodyMustBeSpecOnly, codeContext);
          labeledStatements = prevLblStmts;
          loopStack = prevLoopStack;
        }
        scope.PopMarker();

        if (prevErrorCount == ErrorCount) {
          // determine the Kind and run some additional checks on the body
          if (s.Ens.Count != 0) {
            // The only supported kind with ensures clauses is Proof.
            s.Kind = ForallStmt.ParBodyKind.Proof;
          } else {
            // There are three special cases:
            // * Assign, which is the only kind of the forall statement that allows a heap update.
            // * Call, which is a single call statement with no side effects or output parameters.
            // * A single calc statement, which is a special case of Proof where the postcondition can be inferred.
            // The effect of Assign and the postcondition of Call will be seen outside the forall
            // statement.
            Statement s0 = s.S0;
            if (s0 is AssignStmt) {
              s.Kind = ForallStmt.ParBodyKind.Assign;
            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.ParBodyKind.Call;
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.ParBodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new MaybeFreeExpression(result, true));
              ReportAdditionalInformation(s.Tok, "ensures " + Printer.ExprToString(result) + ";", s.Tok.val.Length);
            } else {
              s.Kind = ForallStmt.ParBodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                Warning(s.Tok, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }
          if (s.Body != null) {
            CheckForallStatementBodyRestrictions(s.Body, s.Kind);
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        ResolveAttributes(s.Mod.Attributes, new ResolveOpts(codeContext, true, true));
        foreach (FrameExpression fe in s.Mod.Expressions) {
          // (yes, say "modifies", not "modify", in the next line -- it seems to give a more readable error message
          ResolveFrameExpression(fe, false, specContextOnly, codeContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, specContextOnly, codeContext);
        }
        s.IsGhost = specContextOnly;

      } else if (stmt is CalcStmt) {
        var prevErrorCount = ErrorCount;
        CalcStmt s = (CalcStmt)stmt;
        s.IsGhost = true;
        if (s.Lines.Count > 0) {
          var e0 = s.Lines.First();
          ResolveExpression(e0, new ResolveOpts(codeContext, true, true));
          Contract.Assert(e0.Type != null);  // follows from postcondition of ResolveExpression
          for (int i = 1; i < s.Lines.Count; i++) {
            if (i < s.Lines.Count - 1 || prevErrorCount == ErrorCount) { // do not resolve the dummy step if there were errors, it might generate more errors
              var e1 = s.Lines[i];
              ResolveExpression(e1, new ResolveOpts(codeContext, true, true));
              Contract.Assert(e1.Type != null);  // follows from postcondition of ResolveExpression
              if (!UnifyTypes(e0.Type, e1.Type)) {
                Error(e1, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, e0.Type);
              } else {
                var step = s.StepOps[i - 1].StepExpr(e0, e1); // Use custom line operator
                ResolveExpression(step, new ResolveOpts(codeContext, true, true));
                s.Steps.Add(step);
              }
              e0 = e1;
            }
          }

          // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
          var prevLblStmts = labeledStatements;
          var prevLoopStack = loopStack;
          labeledStatements = new Scope<Statement>();
          loopStack = new List<Statement>();
          foreach (var h in s.Hints) {
            ResolveStatement(h, true, codeContext);
            CheckHintRestrictions(h);
          }
          labeledStatements = prevLblStmts;
          loopStack = prevLoopStack;

        }
        if (prevErrorCount == ErrorCount && s.Lines.Count > 0) {
          // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
          s.Result = s.ResultOp.StepExpr(s.Lines.First(), s.Lines.Last());
        } else {
          s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Tok, 0), Expression.CreateIntLiteral(s.Tok, 0));
        }
        ResolveExpression(s.Result, new ResolveOpts(codeContext, true, true));
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != ErrorCount || s.Steps.Count == s.Hints.Count);

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        bool bodyIsSpecOnly = specContextOnly;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Source, new ResolveOpts(codeContext, true, specContextOnly));
        Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = ErrorCount == prevErrorCount;
        if (!specContextOnly && successfullyResolved) {
          bodyIsSpecOnly = UsesSpecFeatures(s.Source);
        }
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        if (s.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)s.Source.Type.NormalizeExpand();
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
        var subst = new Dictionary<TypeParameter, Type>();
        Dictionary<string, DatatypeCtor> ctors;
        if (dtd == null) {
          Error(s.Source, "the type of the match source expression must be a datatype (instead found {0})", s.Source.Type);
          ctors = null;
        } else {
          Contract.Assert(sourceType != null);  // dtd and sourceType are set together above
          ctors = datatypeCtors[dtd];
          Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage

          // build the type-parameter substitution map for this use of the datatype
          for (int i = 0; i < dtd.TypeArgs.Count; i++) {
            subst.Add(dtd.TypeArgs[i], sourceType.TypeArgs[i]);
          }
        }
        s.IsGhost = bodyIsSpecOnly;

        ISet<string> memberNamesUsed = new HashSet<string>();
        foreach (MatchCaseStmt mc in s.Cases) {
          DatatypeCtor ctor = null;
          if (ctors != null) {
            Contract.Assert(dtd != null);
            if (!ctors.TryGetValue(mc.Id, out ctor)) {
              Error(mc.tok, "member {0} does not exist in datatype {1}", mc.Id, dtd.Name);
            } else {
              Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
              mc.Ctor = ctor;
              if (ctor.Formals.Count != mc.Arguments.Count) {
                Error(mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", mc.Id, mc.Arguments.Count, ctor.Formals.Count);
              }
              if (memberNamesUsed.Contains(mc.Id)) {
                Error(mc.tok, "member {0} appears in more than one case", mc.Id);
              } else {
                memberNamesUsed.Add(mc.Id);  // add mc.Id to the set of names used
              }
            }
          }
          scope.PushMarker();
          int i = 0;
          foreach (BoundVar v in mc.Arguments) {
            if (!scope.Push(v.Name, v)) {
              Error(v, "Duplicate parameter name: {0}", v.Name);
            }
            ResolveType(v.tok, v.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (ctor != null && i < ctor.Formals.Count) {
              Formal formal = ctor.Formals[i];
              Type st = SubstType(formal.Type, subst);
              if (!UnifyTypes(v.Type, st)) {
                Error(stmt, "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", v.Type, st);
              }
              v.IsGhost = formal.IsGhost;
            }
            i++;
          }
          foreach (Statement ss in mc.Body) {
            ResolveStatement(ss, bodyIsSpecOnly, codeContext);
          }
          scope.PopMarker();
        }
        if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
          // We could complain about the syntactic omission of constructors:
          //   Error(stmt, "match statement does not cover all constructors");
          // but instead we let the verifier do a semantic check.
          // So, for now, record the missing constructors:
          foreach (var ctr in dtd.Ctors) {
            if (!memberNamesUsed.Contains(ctr.Name)) {
              s.MissingCases.Add(ctr);
            }
          }
          Contract.Assert(memberNamesUsed.Count + s.MissingCases.Count == dtd.Ctors.Count);
        }
        if (!s.IsGhost) {
          s.IsGhost = s.Cases.All(cs => cs.Body.All(ss => ss.IsGhost));
        }

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        Error(s.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (s.S != null) {
          ResolveStatement(s.S, specContextOnly, codeContext);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    void FillInDefaultLoopDecreases(LoopStmt loopStmt, Expression guard, List<Expression> theDecreases, ICallable enclosingMethod) {
      Contract.Requires(loopStmt != null);
      Contract.Requires(theDecreases != null);

      if (theDecreases.Count == 0 && guard != null) {
        loopStmt.InferredDecreases = true;
        Expression prefix = null;
        foreach (Expression guardConjunct in Expression.Conjuncts(guard)) {
          Expression guess = null;
          BinaryExpr bin = guardConjunct as BinaryExpr;
          if (bin != null) {
            switch (bin.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.Lt:
              case BinaryExpr.ResolvedOpcode.Le:
                // for A < B and A <= B, use the decreases B - A
                guess = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
              case BinaryExpr.ResolvedOpcode.Gt:
                // for A >= B and A > B, use the decreases A - B
                guess = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                break;
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                if (bin.E0.Type.IsNumericBased()) {
                  // for A != B where A and B are numeric, use the absolute difference between A and B (that is: if A <= B then B-A else A-B)
                  var AminusB = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                  var BminusA = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                  var test = Expression.CreateAtMost(bin.E0, bin.E1);
                  guess = Expression.CreateITE(test, BminusA, AminusB);
                }
                break;
              default:
                break;
            }
          }
          if (guess != null) {
            if (prefix != null) {
              // Make the following guess:  if prefix then guess else -1
              guess = Expression.CreateITE(prefix, guess, Expression.CreateIntLiteral(prefix.tok, -1));
            }
            theDecreases.Add(AutoGeneratedExpression.Create(guess));
            break;  // ignore any further conjuncts
          }
          if (prefix == null) {
            prefix = guardConjunct;
          } else {
            prefix = Expression.CreateAnd(prefix, guardConjunct);
          }
        }
      }
      if (enclosingMethod is IteratorDecl) {
        var iter = (IteratorDecl)enclosingMethod;
        var ie = new IdentifierExpr(loopStmt.Tok, iter.YieldCountVariable.Name);
        ie.Var = iter.YieldCountVariable;  // resolve here
        ie.Type = iter.YieldCountVariable.Type;  // resolve here
        theDecreases.Insert(0, AutoGeneratedExpression.Create(ie));
        loopStmt.InferredDecreases = true;
      }
      if (loopStmt.InferredDecreases) {
        string s = "decreases ";
        if (theDecreases.Count != 0) {
          string sep = "";
          foreach (var d in theDecreases) {
            s += sep + Printer.ExprToString(d);
            sep = ", ";
          }
        }
        s += ";";  // always terminate with a semi-colon, even in the case of an empty decreases clause
        ReportAdditionalInformation(loopStmt.Tok, s, loopStmt.Tok.val.Length);
      }
    }
    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(codeContext != null);

      // First, resolve all LHS's and expression-looking RHS's.
      int errorCountBeforeCheckingLhs = ErrorCount;
      var update = s as UpdateStmt;

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        var ec = ErrorCount;
        ResolveExpression(lhs, new ResolveOpts(codeContext, true, specContextOnly));
        if (ec == ErrorCount) {
          if (update == null && specContextOnly && !AssignStmt.LhsIsToGhost(lhs) && !codeContext.IsGhost) {
            Error(lhs, "cannot assign to non-ghost variable in a ghost context");
          }
          if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
            Error(lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
          }
        }
      }

      // Resolve RHSs
      if (update == null) {
        var suchThat = (AssignSuchThatStmt)s;  // this is the other possible subclass
        ResolveAssignSuchThatStmt(suchThat, specContextOnly, codeContext);
      } else {
        ResolveUpdateStmt(update, specContextOnly, codeContext, errorCountBeforeCheckingLhs);
      }
      ResolveAttributes(s.Attributes, new ResolveOpts(codeContext, true, true));
    }
    /// <summary>
    /// Resolve the RHSs and entire UpdateStmt (LHSs should already have been checked by the caller).
    /// errorCountBeforeCheckingLhs is passed in so that this method can determined if any resolution errors were found during
    /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
    /// </summary>
    private void ResolveUpdateStmt(UpdateStmt update, bool specContextOnly, ICodeContext codeContext, int errorCountBeforeCheckingLhs) {
      Contract.Requires(update != null);
      Contract.Requires(codeContext != null);
      IToken firstEffectfulRhs = null;
      MethodCallInformation methodCallInfo = null;
      var j = 0;
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is TypeRhs) {
          var tr = (TypeRhs)rhs;
          ResolveTypeRhs(tr, update, specContextOnly, codeContext);
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else {
          var er = (ExprRhs)rhs;
          if (er.Expr is ApplySuffix) {
            var a = (ApplySuffix)er.Expr;
            // Note, in the following line, the dontCareAboutCompilation could be more precise. It could be computed as in the else
            // branch if the ApplySuffix is really just the RHS of an assignment. However, if "update" is really a call statement,
            // then we should not let the LHS influence  the call to ResolveApplySuffix. Unfortunately, we don't know which case
            // we're in until ResolveApplySuffix has returned (where a non-null cRhs indicates that "update" is a call statement).
            // So, we'll be conservative and will simply pass in specContextOnly here.
            var cRhs = ResolveApplySuffix(a, new ResolveOpts(codeContext, true, specContextOnly/*see note on previous line*/), true);
            isEffectful = cRhs != null;
            methodCallInfo = methodCallInfo ?? cRhs;
          } else {
            var dontCareAboutCompilation = specContextOnly || (j < update.Lhss.Count && AssignStmt.LhsIsToGhost(update.Lhss[j]));
            ResolveExpression(er.Expr, new ResolveOpts(codeContext, true, dontCareAboutCompilation));
            isEffectful = false;
          }
        }
        if (isEffectful && firstEffectfulRhs == null) {
          firstEffectfulRhs = rhs.Tok;
        }
        j++;
      }

      // figure out what kind of UpdateStmt this is
      if (firstEffectfulRhs == null) {
        if (update.Lhss.Count == 0) {
          Contract.Assert(update.Rhss.Count == 1);  // guaranteed by the parser
          Error(update, "expected method call, found expression");
        } else if (update.Lhss.Count != update.Rhss.Count) {
          Error(update, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", update.Lhss.Count, update.Rhss.Count);
        } else if (ErrorCount == errorCountBeforeCheckingLhs) {
          // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
          for (int i = 0; i < update.Lhss.Count; i++) {
            var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[i].Resolved, update.Rhss[i]);
            update.ResolvedStatements.Add(a);
          }
        }

      } else if (update.CanMutateKnownState) {
        if (1 < update.Rhss.Count) {
          Error(firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
        } else { // it might be ok, if it is a TypeRhs
          Contract.Assert(update.Rhss.Count == 1);
          if (methodCallInfo != null) {
            Error(methodCallInfo.Tok, "cannot have method call in return statement.");
          } else {
            // we have a TypeRhs
            Contract.Assert(update.Rhss[0] is TypeRhs);
            var tr = (TypeRhs)update.Rhss[0];
            Contract.Assert(tr.InitCall != null); // there were effects, so this must have been a call.
            if (tr.CanAffectPreviouslyKnownExpressions) {
              Error(tr.Tok, "can only have initialization methods which modify at most 'this'.");
            } else if (ErrorCount == errorCountBeforeCheckingLhs) {
              var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[0].Resolved, tr);
              update.ResolvedStatements.Add(a);
            }
          }
        }

      } else {
        // if there was an effectful RHS, that must be the only RHS
        if (update.Rhss.Count != 1) {
          Error(firstEffectfulRhs, "an update statement is allowed an effectful RHS only if there is just one RHS");
        } else if (methodCallInfo == null) {
          // must be a single TypeRhs
          if (update.Lhss.Count != 1) {
            Contract.Assert(2 <= update.Lhss.Count);  // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
            Error(update.Lhss[1].tok, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", update.Lhss.Count, update.Rhss.Count);
          } else if (ErrorCount == errorCountBeforeCheckingLhs) {
            var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[0].Resolved, update.Rhss[0]);
            update.ResolvedStatements.Add(a);
          }
        } else if (ErrorCount == errorCountBeforeCheckingLhs) {
          // a call statement
          var resolvedLhss = new List<Expression>();
          foreach (var ll in update.Lhss) {
            resolvedLhss.Add(ll.Resolved);
          }
          var a = new CallStmt(methodCallInfo.Tok, update.EndTok, resolvedLhss, methodCallInfo.Callee, methodCallInfo.Args);
          update.ResolvedStatements.Add(a);
        }
      }

      foreach (var a in update.ResolvedStatements) {
        ResolveStatement(a, specContextOnly, codeContext);
      }
      update.IsGhost = update.ResolvedStatements.TrueForAll(ss => ss.IsGhost);
    }

    private void ResolveAssignSuchThatStmt(AssignSuchThatStmt s, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);

      var varLhss = new List<IVariable>();
      if (s.AssumeToken == null) {
        // to ease in the verification of the existence check, only allow local variables as LHSs
        foreach (var lhs in s.Lhss) {
          var ide = lhs.Resolved as IdentifierExpr;
          if (ide == null) {
            Error(lhs, "the assign-such-that statement currently only supports local-variable LHSs");
          } else {
            varLhss.Add(ide.Var);
          }
        }
      }

      s.IsGhost = s.Lhss.TrueForAll(AssignStmt.LhsIsToGhost);
      var ec = ErrorCount;
      ResolveExpression(s.Expr, new ResolveOpts(codeContext, true, specContextOnly));
      if (ec == ErrorCount && !s.IsGhost && s.AssumeToken == null && !specContextOnly) {
        CheckIsNonGhost(s.Expr);

        var missingBounds = new List<IVariable>();
        CheckTypeInference(s.Expr);  // we need to resolve operators before the call to DiscoverBoundsAux
        var allBounds = DiscoverBoundsAux(s.Tok, varLhss, s.Expr, true, true, true, missingBounds);
        if (missingBounds.Count != 0) {
          s.MissingBounds = missingBounds;  // so that an error message can be produced during compilation
        } else {
          Contract.Assert(allBounds != null);
          s.Bounds = new List<ComprehensionExpr.BoundedPool>();
          foreach (var pair in allBounds) {
            Contract.Assert(1 <= pair.Item2.Count);
            // TODO: The following could be improved by picking the bound that is most likely to give rise to an efficient compiled program
            s.Bounds.Add(pair.Item2[0]);
          }
        }
      }
    }

    bool ResolveAlternatives(List<GuardedAlternative> alternatives, bool specContextOnly, AlternativeLoopStmt loopToCatchBreaks, ICodeContext codeContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(codeContext != null);

      bool isGhost = specContextOnly;
      // first, resolve the guards, which tells us whether or not the entire statement is a ghost statement
      foreach (var alternative in alternatives) {
        int prevErrorCount = ErrorCount;
        ResolveExpression(alternative.Guard, new ResolveOpts(codeContext, true, specContextOnly));
        Contract.Assert(alternative.Guard.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = ErrorCount == prevErrorCount;
        if (!UnifyTypes(alternative.Guard.Type, Type.Bool)) {
          Error(alternative.Guard, "condition is expected to be of type {0}, but is {1}", Type.Bool, alternative.Guard.Type);
        }
        if (!specContextOnly && successfullyResolved) {
          isGhost = isGhost || UsesSpecFeatures(alternative.Guard);
        }
      }

      if (loopToCatchBreaks != null) {
        loopStack.Add(loopToCatchBreaks);  // push
        if (loopToCatchBreaks.Labels == null) {  // otherwise, "loopToCatchBreak" is already in "inSpecOnlyContext" map
          inSpecOnlyContext.Add(loopToCatchBreaks, specContextOnly);
        }
      }
      foreach (var alternative in alternatives) {
        scope.PushMarker();
        foreach (Statement ss in alternative.Body) {
          ResolveStatement(ss, isGhost, codeContext);
        }
        scope.PopMarker();
      }
      if (loopToCatchBreaks != null) {
        loopStack.RemoveAt(loopStack.Count - 1);  // pop
      }

      return isGhost;
    }

    /// <summary>
    /// Resolves the given call statement.
    /// Assumes all LHSs have already been resolved (and checked for mutability).
    /// </summary>
    void ResolveCallStmt(CallStmt s, bool specContextOnly, ICodeContext codeContext, Type receiverType) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);
      bool isInitCall = receiverType != null;

      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      if (!isInitCall && callee is Constructor) {
        Error(s, "a constructor is allowed to be called only when an object is being allocated");
      }
      s.IsGhost = callee.IsGhost;
      if (specContextOnly && !callee.IsGhost) {
        Error(s, "only ghost methods can be called from this context");
      }

      // resolve left-hand sides
      foreach (var lhs in s.Lhs) {
        Contract.Assume(lhs.Type != null);  // a sanity check that LHSs have already been resolved
      }
      // resolve arguments
      if (!s.IsGhost && s.Receiver.WasResolved()) {
        CheckIsNonGhost(s.Receiver);
      }
      int j = 0;
      foreach (Expression e in s.Args) {
        bool allowGhost = s.IsGhost || callee.Ins.Count <= j || callee.Ins[j].IsGhost;
        var ec = ErrorCount;
        ResolveExpression(e, new ResolveOpts(codeContext, true, allowGhost));
        if (ec == ErrorCount && !allowGhost) {
          CheckIsNonGhost(e);
        }
        j++;
      }

      if (callee.Ins.Count != s.Args.Count) {
        Error(s, "wrong number of method arguments (got {0}, expected {1})", s.Args.Count, callee.Ins.Count);
      } else if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          Error(s, "a method called as an initialization method must not have any result arguments");
        } else {
          Error(s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
        }
      } else {
        if (isInitCall) {
          if (callee.IsStatic) {
            Error(s.Tok, "a method called as an initialization method must not be 'static'");
          }
        } else if (!callee.IsStatic) {
          if (!scope.AllowInstance && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            Error(s.Receiver, "'this' is not allowed in a 'static' context");
          } else if (s.Receiver is StaticReceiverExpr) {
            Error(s.Receiver, "call to instance method requires an instance");
          }
        }
        // type check the arguments
        for (int i = 0; i < callee.Ins.Count; i++) {
          Type st = SubstType(callee.Ins[i].Type, s.MethodSelect.TypeArgumentSubstitutions());
          if (!UnifyTypes(cce.NonNull(s.Args[i].Type), st)) {
            Error(s, "incorrect type of method in-parameter {0} (expected {1}, got {2})", i, st, s.Args[i].Type);
          }
        }
        for (int i = 0; i < callee.Outs.Count; i++) {
          Type st = SubstType(callee.Outs[i].Type, s.MethodSelect.TypeArgumentSubstitutions());
          var lhs = s.Lhs[i];
          if (!UnifyTypes(cce.NonNull(lhs.Type), st)) {
            Error(s, "incorrect type of method out-parameter {0} (expected {1}, got {2})", i, st, lhs.Type);
          } else {
            var resolvedLhs = lhs.Resolved;
            if (!specContextOnly && (s.IsGhost || callee.Outs[i].IsGhost)) {
              // LHS must denote a ghost
              if (resolvedLhs is IdentifierExpr) {
                var ll = (IdentifierExpr)resolvedLhs;
                if (!ll.Var.IsGhost) {
                  if (ll is AutoGhostIdentifierExpr && ll.Var is LocalVariable) {
                    // the variable was actually declared in this statement, so auto-declare it as ghost
                    ((LocalVariable)ll.Var).MakeGhost();
                  } else {
                    Error(s, "actual out-parameter {0} is required to be a ghost variable", i);
                  }
                }
              } else if (resolvedLhs is MemberSelectExpr) {
                var ll = (MemberSelectExpr)resolvedLhs;
                if (!ll.Member.IsGhost) {
                  Error(s, "actual out-parameter {0} is required to be a ghost field", i);
                }
              } else {
                // this is an array update, and arrays are always non-ghost
                Error(s, "actual out-parameter {0} is required to be a ghost variable", i);
              }
            }
            // LHS must denote a mutable field.
            CheckIsLvalue(resolvedLhs, codeContext);
          }
        }

        // Resolution termination check
        ModuleDefinition callerModule = codeContext.EnclosingModule;
        ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
        if (callerModule == calleeModule) {
          // intra-module call; add edge in module's call graph
          var caller = codeContext as ICallable;
          if (caller == null) {
            // don't add anything to the call graph after all
          } else if (caller is IteratorDecl) {
            callerModule.CallGraph.AddEdge(((IteratorDecl)caller).Member_MoveNext, callee);
          } else {
            callerModule.CallGraph.AddEdge(caller, callee);
            if (caller == callee) {
              callee.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
            }
          }
        }
      }
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !codeContext.AllowsNontermination) {
        Error(s.Tok, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs, ICodeContext codeContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(codeContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          Error(lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          Error(lhs, "LHS of assignment must denote a mutable field");
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        if (!UnifyTypes(ll.Seq.Type, ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), codeContext))) {
          Error(ll.Seq, "LHS of array assignment must denote an array element (found {0})", ll.Seq.Type);
        }
        if (!ll.SelectOne) {
          Error(ll.Seq, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        Error(lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }

    void ResolveBlockStatement(BlockStmt blockStmt, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(codeContext != null);

      foreach (Statement ss in blockStmt.Body) {
        labeledStatements.PushMarker();
        // push labels
        for (var l = ss.Labels; l != null; l = l.Next) {
          var lnode = l.Data;
          Contract.Assert(lnode.Name != null);  // LabelNode's with .Label==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
          var prev = labeledStatements.Find(lnode.Name);
          if (prev == ss) {
            Error(lnode.Tok, "duplicate label");
          } else if (prev != null) {
            Error(lnode.Tok, "label shadows an enclosing label");
          } else {
            bool b = labeledStatements.Push(lnode.Name, ss);
            Contract.Assert(b);  // since we just checked for duplicates, we expect the Push to succeed
            if (l == ss.Labels) {  // add it only once
              inSpecOnlyContext.Add(ss, specContextOnly);
            }
          }
        }
        ResolveStatement(ss, specContextOnly, codeContext);
        labeledStatements.PopMarker();
      }
    }

    /// <summary>
    /// This method performs some additional checks on the body "stmt" of a forall statement of kind "kind".
    /// </summary>
    public void CheckForallStatementBodyRestrictions(Statement stmt, ForallStmt.ParBodyKind kind) {
      Contract.Requires(stmt != null);
      if (stmt is PredicateStmt) {
        // cool
      } else if (stmt is PrintStmt) {
        Error(stmt, "print statement is not allowed inside a forall statement");
      } else if (stmt is BreakStmt) {
        // this case is checked already in the first pass through the forall-statement body, by doing so from an empty set of labeled statements and resetting the loop-stack
      } else if (stmt is ReturnStmt) {
        Error(stmt, "return statement is not allowed inside a forall statement");
      } else if (stmt is YieldStmt) {
        Error(stmt, "yield statement is not allowed inside a forall statement");
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckForallStatementBodyLhs(s.Tok, lhs.Resolved, kind);
        }
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckForallStatementBodyRestrictions(ss, kind);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Update != null) {
          CheckForallStatementBodyRestrictions(s.Update, kind);
        }
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        CheckForallStatementBodyLhs(s.Tok, s.Lhs.Resolved, kind);
        var rhs = s.Rhs;  // ExprRhs and HavocRhs are fine, but TypeRhs is not
        if (rhs is TypeRhs) {
          if (kind == ForallStmt.ParBodyKind.Assign) {
            Error(rhs.Tok, "new allocation not supported in forall statements");
          } else {
            Error(rhs.Tok, "new allocation not allowed in ghost context");
          }
        }
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        foreach (var lhs in s.Lhs) {
          var idExpr = lhs as IdentifierExpr;
          if (idExpr != null) {
            if (scope.ContainsDecl(idExpr.Var)) {
              Error(stmt, "body of forall statement is attempting to update a variable declared outside the forall statement");
            }
          } else {
            Error(stmt, "the body of the enclosing forall statement is not allowed to update heap locations");
          }
        }
        if (s.Method.Mod.Expressions.Count != 0) {
          Error(stmt, "the body of the enclosing forall statement is not allowed to update heap locations, so any call must be to a method with an empty modifies clause");
        }
        if (!s.Method.IsGhost) {
          // The reason for this restriction is that the compiler is going to omit the forall statement altogether--it has
          // no effect.  However, print effects are not documented, so to make sure that the compiler does not omit a call to
          // a method that prints something, all calls to non-ghost methods are disallowed.  (Note, if this restriction
          // is somehow lifted in the future, then it is still necessary to enforce s.Method.Mod.Expressions.Count != 0 for
          // calls to non-ghost methods.)
          Error(s, "the body of the enclosing forall statement is not allowed to call non-ghost methods");
        }

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        foreach (var ss in s.Body) {
          CheckForallStatementBodyRestrictions(ss, kind);
        }
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        CheckForallStatementBodyRestrictions(s.Thn, kind);
        if (s.Els != null) {
          CheckForallStatementBodyRestrictions(s.Els, kind);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        if (s.Body != null) {
          CheckForallStatementBodyRestrictions(s.Body, kind);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        switch (s.Kind) {
          case ForallStmt.ParBodyKind.Assign:
            Error(stmt, "a forall statement with heap updates is not allowed inside the body of another forall statement");
            break;
          case ForallStmt.ParBodyKind.Call:
          case ForallStmt.ParBodyKind.Proof:
            // these are fine, since they don't update any non-local state
            break;
          default:
            Contract.Assert(false);  // unexpected kind
            break;
        }

      } else if (stmt is CalcStmt) {
          // cool

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          foreach (var ss in kase.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    void CheckForallStatementBodyLhs(IToken tok, Expression lhs, ForallStmt.ParBodyKind kind) {
      var idExpr = lhs as IdentifierExpr;
      if (idExpr != null) {
        if (scope.ContainsDecl(idExpr.Var)) {
          Error(tok, "body of forall statement is attempting to update a variable declared outside the forall statement");
        }
      } else if (kind != ForallStmt.ParBodyKind.Assign) {
        Error(tok, "the body of the enclosing forall statement is not allowed to update heap locations");
      }
    }

    /// <summary>
    /// Check that a statment is a valid hint for a calculation.
    /// ToDo: generalize the part for compound statements to take a delegate?
    /// </summary>
    public void CheckHintRestrictions(Statement stmt) {
      Contract.Requires(stmt != null);
      if (stmt is PredicateStmt) {
        // cool
      } else if (stmt is PrintStmt) {
        // not allowed in ghost context
      } else if (stmt is BreakStmt) {
        // already checked while resolving hints
      } else if (stmt is ReturnStmt) {
        Error(stmt, "return statement is not allowed inside a hint");
      } else if (stmt is YieldStmt) {
        Error(stmt, "yield statement is not allowed inside a hint");
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckHintLhs(s.Tok, lhs.Resolved);
        }
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        CheckHintLhs(s.Tok, s.Lhs.Resolved);
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        if (s.Method.Mod.Expressions.Count != 0) {
          Error(stmt, "calls to methods with side-effects are not allowed inside a hint");
        }
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckHintRestrictions(ss);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Update != null) {
          CheckHintRestrictions(s.Update);
        }
      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        foreach (var ss in s.Body) {
          CheckHintRestrictions(ss);
        }
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        CheckHintRestrictions(s.Thn);
        if (s.Els != null) {
          CheckHintRestrictions(s.Els);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckHintRestrictions(ss);
          }
        }

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        if (s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
          Error(s.Mod.Expressions[0].tok, "a while statement used inside a hint is not allowed to have a modifies clause");
        }
        if (s.Body != null) {
          CheckHintRestrictions(s.Body);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckHintRestrictions(ss);
          }
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        switch (s.Kind) {
          case ForallStmt.ParBodyKind.Assign:
            Error(stmt, "a forall statement with heap updates is not allowed inside a hint");
            break;
          case ForallStmt.ParBodyKind.Call:
          case ForallStmt.ParBodyKind.Proof:
            // these are fine, since they don't update any non-local state
            break;
          default:
            Contract.Assert(false);  // unexpected kind
            break;
        }

      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        foreach (var h in s.Hints) {
          CheckHintRestrictions(h);
        }

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          foreach (var ss in kase.Body) {
            CheckHintRestrictions(ss);
          }
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    void CheckHintLhs(IToken tok, Expression lhs) {
      var idExpr = lhs as IdentifierExpr;
      if (idExpr == null) {
        Error(tok, "a hint is not allowed to update heap locations");
      } else if (scope.ContainsDecl(idExpr.Var)) {
        Error(tok, "a hint is not allowed to update a variable declared outside the hint");
      }
    }

    Type ResolveTypeRhs(TypeRhs rr, Statement stmt, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      // "new" is not allowed in ghost contexts
      if (specContextOnly) {
        Error(rr.Tok, "'new' is not allowed in ghost contexts");
      }
      if (rr.Type == null) {
        if (rr.ArrayDimensions != null) {
          // ---------- new T[EE]
          Contract.Assert(rr.Arguments == null && rr.Path == null && rr.InitCall == null);
          ResolveType(stmt.Tok, rr.EType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          int i = 0;
          foreach (Expression dim in rr.ArrayDimensions) {
            Contract.Assert(dim != null);
            ResolveExpression(dim, new ResolveOpts(codeContext, true));
            if (!UnifyTypes(dim.Type, new OperationTypeProxy(true, false, false, false, false))) {
              Error(stmt, "new must use an integer-based expression for the array size (got {0} for index {1})", dim.Type, i);
            }
            i++;
          }
          rr.Type = ResolvedArrayType(stmt.Tok, rr.ArrayDimensions.Count, rr.EType, codeContext);
        } else {
          bool callsConstructor = false;
          if (rr.Arguments == null) {
            ResolveType(stmt.Tok, rr.EType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (!rr.EType.IsRefType) {
              Error(stmt, "new can be applied only to reference types (got {0})", rr.EType);
            }
          } else {
            string initCallName = null;
            IToken initCallTok = null;
            // Resolve rr.Path and do one of three things:
            // * If rr.Path denotes a type, then set EType,initCallName to rr.Path,"_ctor", which sets up a call to the anonymous constructor.
            // * If the all-but-last components of rr.Path denote a type, then do EType,initCallName := allButLast(EType),last(EType)
            // * Otherwise, report an error
            var ret = ResolveTypeLenient(rr.Tok, rr.Path, codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
            if (ret != null) {
              // The all-but-last components of rr.Path denote a type (namely, ret.ReplacementType).
              rr.EType = ret.ReplacementType;
              initCallName = ret.LastComponent.SuffixName;
              initCallTok = ret.LastComponent.tok;
            } else {
              // Either rr.Path resolved correctly as a type or there was no way to drop a last component to make it into something that looked
              // like a type.  In either case, set EType,initCallName to Path,"_ctor" and continue.
              rr.EType = rr.Path;
              initCallName = "_ctor";
              initCallTok = rr.Tok;
            }
            if (!rr.EType.IsRefType) {
              Error(stmt, "new can be applied only to reference types (got {0})", rr.EType);
            } else {
              // ---------- new C.Init(EE)
              Contract.Assert(initCallName != null);
              var prevErrorCount = ErrorCount;

              // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
              // type, create an dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
              var lhs = new ImplicitThisExpr(initCallTok) { Type = rr.EType };
              var callLhs = new ExprDotName(initCallTok, lhs, initCallName, ret == null ? null : ret.LastComponent.OptTypeArguments);
              ResolveDotSuffix(callLhs, true, rr.Arguments, new ResolveOpts(codeContext, true, specContextOnly), true);
              if (prevErrorCount == ErrorCount) {
                Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
                var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
                if (methodSel.Member is Method) {
                  rr.InitCall = new CallStmt(initCallTok, stmt.EndTok, new List<Expression>(), methodSel, rr.Arguments);
                  ResolveCallStmt(rr.InitCall, specContextOnly, codeContext, rr.EType);
                  if (rr.InitCall.Method is Constructor) {
                    callsConstructor = true;
                  }
                } else {
                  Error(initCallTok, "object initialization must denote an initializing method or constructor ({0})", initCallName);
                }
              }
            }
          }
          if (rr.EType.IsRefType) {
            var udt = rr.EType.NormalizeExpand() as UserDefinedType;
            if (udt != null) {
              var cl = (ClassDecl)udt.ResolvedClass;  // cast is guaranteed by the call to rr.EType.IsRefType above, together with the "rr.EType is UserDefinedType" test
              if (cl is TraitDecl) {
                Error(stmt, "new cannot be applied to a trait");
              }
              if (!callsConstructor && cl.HasConstructor) {
                Error(stmt, "when allocating an object of type '{0}', one of its constructor methods must be called", cl.Name);
              }
            }
          }
          rr.Type = rr.EType;
        }
      }
      return rr.Type;
    }

    MemberDecl ResolveMember(IToken tok, Type receiverType, string memberName, out NonProxyType nptype) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out nptype) != null);

      nptype = null;  // prepare for the worst
      receiverType = receiverType.NormalizeExpand();
      var opProxy = receiverType as OperationTypeProxy;
      if (opProxy != null) {
        if (opProxy.JustInts) {
          // close enough to do member lookups for int-based types
          receiverType = Type.Int;
        } else if (opProxy.JustReals) {
          // close enough to do member lookups for real-based types
          receiverType = Type.Real;
        }
      }
      if (receiverType is TypeProxy) {
        Error(tok, "type of the receiver is not fully determined at this program point", receiverType);
        return null;
      }
      Contract.Assert(receiverType is NonProxyType);  // there are only two kinds of types: proxies and non-proxies

      UserDefinedType ctype = UserDefinedType.DenotesClass(receiverType);
      if (ctype != null) {
        var cd = (ClassDecl)ctype.ResolvedClass;  // correctness of cast follows from postcondition of DenotesClass
        Contract.Assert(ctype.TypeArgs.Count == cd.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[cd].TryGetValue(memberName, out member)) {
          var kind = cd is IteratorDecl ? "iterator" : "class";
          if (memberName == "_ctor") {
            Error(tok, "{0} {1} does not have an anonymous constructor", kind, ctype.Name);
          } else {
            Error(tok, "member {0} does not exist in {2} {1}", memberName, ctype.Name, kind);
          }
          return null;
        } else {
          nptype = ctype;
          return member;
        }
      }

      DatatypeDecl dtd = receiverType.AsDatatype;
      if (dtd != null) {
        MemberDecl member;
        if (!datatypeMembers[dtd].TryGetValue(memberName, out member)) {
          Error(tok, "member {0} does not exist in datatype {1}", memberName, dtd.Name);
          return null;
        } else {
          nptype = (UserDefinedType)receiverType;
          return member;
        }
      }

      BasicTypeVariety basic;
      if (receiverType.IsBoolType) {
        basic = BasicTypeVariety.Bool;
      } else if (receiverType.IsNumericBased(Type.NumericPersuation.Int)) {
        basic = BasicTypeVariety.Int;
      } else if (receiverType.IsNumericBased(Type.NumericPersuation.Real)) {
        basic = BasicTypeVariety.Real;
      } else {
        basic = BasicTypeVariety.None;
      }
      if (basic != BasicTypeVariety.None) {
        MemberDecl member;
        if (basicTypeMembers[(int)basic].TryGetValue(memberName, out member)) {
          nptype = (NonProxyType)receiverType;
          return member;
        }
      }

      Error(tok, "type {0} does not have a member {1}", receiverType, memberName);
      return null;
    }

    /// <summary>
    /// Returns a resolved MemberSelectExpr for a field.
    /// </summary>
    public static MemberSelectExpr NewMemberSelectExpr(IToken tok, Expression obj, Field field, Dictionary<TypeParameter, Type> typeSubstMap) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(field != null);
      Contract.Requires(obj.Type != null);  // "obj" is required to be resolved
      var e = new MemberSelectExpr(tok, obj, field.Name);
      e.Member = field;  // resolve here
      e.Type = typeSubstMap == null ? field.Type : SubstType(field.Type, typeSubstMap);  // resolve here
      return e;
    }

    public static Dictionary<TypeParameter, Type> TypeSubstitutionMap(List<TypeParameter> formals, List<Type> actuals) {
      Contract.Requires(formals != null);
      Contract.Requires(actuals != null);
      Contract.Requires(formals.Count == actuals.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < formals.Count; i++) {
        subst.Add(formals[i], actuals[i]);
      }
      return subst;
    }

    /// <summary>
    /// If the substitution has no effect, the return value is pointer-equal to 'type'
    /// </summary>
    public static Type SubstType(Type type, Dictionary<TypeParameter, Type> subst) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      if (type is BasicType) {
        return type;
      } else if (type is MapType) {
        var t = (MapType)type;
        var dom = SubstType(t.Domain, subst);
        var ran = SubstType(t.Range, subst);
        if (dom == t.Domain && ran == t.Range) {
          return type;
        } else {
          return new MapType(t.Finite, dom, ran);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var arg = SubstType(t.Arg, subst);
        if (arg == t.Arg) {
          return type;
        } else if (type is SetType) {
          return new SetType(arg);
        } else if (type is MultiSetType) {
          return new MultiSetType(arg);
        } else if (type is SeqType) {
          return new SeqType(arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected collection type
        }
      } else if (type is ArrowType) {
        var t = (ArrowType)type;
        var at = new ArrowType(t.tok, t.Args.ConvertAll(u => SubstType(u, subst)), SubstType(t.Result, subst));
        at.ResolvedClass = t.ResolvedClass;
        return at;
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedParam != null) {
          Type s;
          if (subst.TryGetValue(t.ResolvedParam, out s)) {
            Contract.Assert(t.TypeArgs.Count == 0); // what to do?
            return cce.NonNull(s);
          } else {
            if (t.TypeArgs.Count == 0) {
              return type;
            } else {
              return new UserDefinedType(t.ResolvedParam) {
                TypeArgs = t.TypeArgs.ConvertAll(u => SubstType(u, subst))
              };
            }
          }
        } else if (t.ResolvedClass != null) {
          List<Type> newArgs = null;  // allocate it lazily
          var resolvedClass = t.ResolvedClass;
#if TEST_TYPE_SYNONYM_TRANSPARENCY
          if (resolvedClass is TypeSynonymDecl && resolvedClass.Name == "type#synonym#transparency#test") {
            // Usually, all type parameters mentioned in the definition of a type synonym are also type parameters
            // to the type synonym itself, but in this instrumented testing, that is not so, so we also do a substitution
            // in the .Rhs of the synonym.
            var syn = (TypeSynonymDecl)resolvedClass;
            var r = SubstType(syn.Rhs, subst);
            if (r != syn.Rhs) {
              resolvedClass = new TypeSynonymDecl(syn.tok, syn.Name, syn.TypeArgs, syn.Module, r, null);
              newArgs = new List<Type>();
            }
          }
#endif
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            Type s = SubstType(p, subst);
            if (s != p && newArgs == null) {
              // lazily construct newArgs
              newArgs = new List<Type>();
              for (int j = 0; j < i; j++) {
                newArgs.Add(t.TypeArgs[j]);
              }
            }
            if (newArgs != null) {
              newArgs.Add(s);
            }
          }
          if (newArgs == null) {
            // there were no substitutions
            return type;
          } else {
            // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
            return new UserDefinedType(t.tok, t.Name, resolvedClass, newArgs);
          }
        } else {
          // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
          // properly resolved; just return it
          return type;
        }
      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T == null) {
          return type;
        }
        var s = SubstType(t.T, subst);
        return s == t.T ? type : s;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public static UserDefinedType GetThisType(IToken tok, ClassDecl cl) {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return UserDefinedType.FromTopLevelDecl(tok, cl);
    }

    /// <summary>
    /// Requires "member" to be declared in a class.
    /// </summary>
    public static UserDefinedType GetReceiverType(IToken tok, MemberDecl member) {
      Contract.Requires(tok != null);
      Contract.Requires(member != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return GetThisType(tok, (ClassDecl)member.EnclosingClass);
    }

    public class ResolveOpts
    {
      public readonly ICodeContext codeContext;
      public readonly bool twoState;
      public readonly bool DontCareAboutCompilation;
      public ResolveOpts(ICodeContext codeContext, bool twoState) {
        Contract.Requires(codeContext != null);
        this.codeContext = codeContext;
        this.twoState = twoState;
        DontCareAboutCompilation = codeContext.IsGhost;
      }
      public ResolveOpts(ICodeContext codeContext, bool twoState, bool dontCareAboutCompilation) {
        Contract.Requires(codeContext != null);
        this.codeContext = codeContext;
        this.twoState = twoState;
        this.DontCareAboutCompilation = dontCareAboutCompilation;
      }
      public ResolveOpts(ResolveOpts r, bool dontCareAboutCompilation) {
        Contract.Requires(r != null);
        this.codeContext = r.codeContext;
        this.twoState = r.twoState;
        this.DontCareAboutCompilation = dontCareAboutCompilation;
      }
    }

    /// <summary>
    /// "twoState" implies that "old" and "fresh" expressions are allowed.
    /// </summary>
    public void ResolveExpression(Expression expr, ResolveOpts opts) {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
      ResolveExpressionX(expr, opts);
      // For testing purposes, change the type of "expr" to a type synonym (mwo-ha-ha-ha!)
      var t = expr.Type;
      Contract.Assert(t != null);
      var sd = new TypeSynonymDecl(expr.tok, "type#synonym#transparency#test", new List<TypeParameter>(), codeContext.EnclosingModule, t, null);
      var ts = new UserDefinedType(expr.tok, "type#synonym#transparency#test", sd, new List<Type>(), null);
      expr.DebugTest_ChangeType(ts);
    }
    public void ResolveExpressionX(Expression expr, ResolveOpts opts) {
#endif
      Contract.Requires(expr != null);
      Contract.Requires(opts != null);
      Contract.Ensures(expr.Type != null);
      if (expr.Type != null) {
        // expression has already been resovled
        return;
      }

      // The following cases will resolve the subexpressions and will attempt to assign a type of expr.  However, if errors occur
      // and it cannot be determined what the type of expr is, then it is fine to leave expr.Type as null.  In that case, the end
      // of this method will assign proxy type to the expression, which reduces the number of error messages that are produced
      // while type checking the rest of the program.

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        var errorCount = ErrorCount;
        ResolveExpression(e.E, opts);
        e.Type = e.E.Type;
        if (errorCount != ErrorCount) {
          // there were errors resolving the operand; take the quick way out and
          // just let the (already erronous) subexpression be what the negation expression
          // will resolve to
          e.ResolvedExpression = e.E;
        } else {
          Expression zero;
          if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
            // we know for sure that this is a real-based unary minus
            zero = new LiteralExpr(e.tok, Basetypes.BigDec.ZERO);
          } else {
            // it may be an int-based operand or it may be that we don't know yet; we'll treat
            // two cases the same way
            zero = new LiteralExpr(e.tok, 0);
          }
          var subtract = new BinaryExpr(e.tok, BinaryExpr.Opcode.Sub, zero, e.E);
          // Resolve the subtraction expression.  This look like it will resolve e.E once more,
          // but the recursive calls to the resolver is mindful about DAGs and will check if the
          // subexpression has already been resolved.
          ResolveExpression(subtract, opts);
          e.ResolvedExpression = subtract;
        }

      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr) {
          StaticReceiverExpr eStatic = (StaticReceiverExpr)e;
          this.ResolveType(eStatic.tok, eStatic.UnresolvedType, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.Type = eStatic.UnresolvedType;
        } else {
          if (e.Value == null) {
            e.Type = new ObjectTypeProxy();
          } else if (e.Value is BigInteger) {
            e.Type = new OperationTypeProxy(true, false, false, false, false);
          } else if (e.Value is Basetypes.BigDec) {
            e.Type = new OperationTypeProxy(false, true, false, false, false);
          } else if (e.Value is bool) {
            e.Type = Type.Bool;
          } else if (e is CharLiteralExpr) {
            e.Type = Type.Char;
          } else if (e is StringLiteralExpr) {
            e.Type = new UserDefinedType(e.tok, "string", (List<Type>)null);
            ResolveType(e.tok, e.Type, opts.codeContext, ResolveTypeOptionEnum.DontInfer, null);
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
          }
        }
      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          Error(expr, "'this' is not allowed in a 'static' context");
        }
        if (currentClass != null) {
          expr.Type = GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var != null) {
          expr.Type = e.Var.Type;
        } else {
          Error(expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        }

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        TopLevelDecl d;
        if (!moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out d)) {
          Error(expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (ReallyAmbiguousTopLevelDecl(ref d)) {
          Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", dtv.DatatypeName, ((AmbiguousTopLevelDecl)d).ModuleNames());
        } else if (!(d is DatatypeDecl)) {
          Error(expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        } else {
          ResolveDatatypeValue(opts, dtv, (DatatypeDecl)d);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy();
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, opts);
          Contract.Assert(ee.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(elementType, ee.Type)) {
            Error(ee, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", ee.Type, elementType);
          }
        }
        if (expr is SetDisplayExpr) {
          expr.Type = new SetType(elementType);
        } else if (expr is MultiSetDisplayExpr) {
          expr.Type = new MultiSetType(elementType);
        } else {
          expr.Type = new SeqType(elementType);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        foreach (ExpressionPair p in e.Elements) {
          ResolveExpression(p.A, opts);
          Contract.Assert(p.A.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(domainType, p.A.Type)) {
            Error(p.A, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", p.A.Type, domainType);
          }
          ResolveExpression(p.B, opts);
          Contract.Assert(p.B.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(rangeType, p.B.Type)) {
            Error(p.B, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", p.B.Type, rangeType);
          }
        }
        expr.Type = new MapType(e.Finite, domainType, rangeType);
      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, opts, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          Error(e.tok, "name of module ({0}) is used as a variable", e.Name);
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          Error(e.tok, "name of type ({0}) is used as a variable", e.Name);
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, opts, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          Error(e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          Error(e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
        }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        ResolveApplySuffix(e, opts, false);

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        ResolveExpression(e.Obj, opts);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        NonProxyType nptype;
        MemberDecl member = ResolveMember(expr.tok, e.Obj.Type, e.MemberName, out nptype);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (member is Function) {
          var fn = member as Function;
          e.Member = fn;
          // build the type substitution map
          e.TypeApplication = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = nptype as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            // instantiate all type arguments from the functions. no polymorphic application
            e.TypeApplication.AddRange(ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication.Add(prox);
          }
          e.Type = new ArrowType(fn.tok, fn.Formals.ConvertAll(f => SubstType(f.Type, subst)), SubstType(fn.ResultType, subst), builtIns.SystemModule);
          AddCallGraphEdge(opts.codeContext, fn, e);
        } else if (member is Field) {
          var field = (Field)member;
          e.Member = field;
          if (e.Obj is StaticReceiverExpr) {
            Error(expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = nptype as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = SubstType(field.Type, subst);
          }
        } else {
          Error(expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, nptype);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, opts, true);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, opts);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        if (!UnifyTypes(e.Array.Type, ResolvedArrayType(e.Array.tok, e.Indices.Count, elementType, opts.codeContext))) {
          Error(e.Array, "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        }
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, opts);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(idx.Type, new OperationTypeProxy(true, false, false, false, false))) {
            Error(idx, "array selection requires integer-based numeric indices (got {0} for index {1})", idx.Type, i);
          }
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, opts);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        if (UnifyTypes(e.Seq.Type, new SeqType(elementType))) {
          ResolveExpression(e.Index, opts);
          Contract.Assert(e.Index.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Index.Type, Type.Int)) {
            Error(e.Index, "sequence update requires integer index (got {0})", e.Index.Type);
          }
          ResolveExpression(e.Value, opts);
          Contract.Assert(e.Value.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Value.Type, elementType)) {
            Error(e.Value, "sequence update requires the value to have the element type of the sequence (got {0})", e.Value.Type);
          }
          expr.Type = e.Seq.Type;
        } else if (UnifyTypes(e.Seq.Type, new MapType(true, domainType, rangeType))) {
          ResolveExpression(e.Index, opts);
          if (!UnifyTypes(e.Index.Type, domainType)) {
            Error(e.Index, "map update requires domain element to be of type {0} (got {1})", domainType, e.Index.Type);
          }
          ResolveExpression(e.Value, opts);
          if (!UnifyTypes(e.Value.Type, rangeType)) {
            Error(e.Value, "map update requires the value to have the range type {0} (got {1})", rangeType, e.Value.Type);
          }
          expr.Type = e.Seq.Type;
        } else if (UnifyTypes(e.Seq.Type, new MapType(false, domainType, rangeType))) {
          ResolveExpression(e.Index, opts);
          if (!UnifyTypes(e.Index.Type, domainType)) {
            Error(e.Index, "imap update requires domain element to be of type {0} (got {1})", domainType, e.Index.Type);
          }
          ResolveExpression(e.Value, opts);
          if (!UnifyTypes(e.Value.Type, rangeType)) {
            Error(e.Value, "imap update requires the value to have the range type {0} (got {1})", rangeType, e.Value.Type);
          }
          expr.Type = e.Seq.Type;
        } else if (UnifyTypes(e.Seq.Type, new MultiSetType(elementType))) {
          ResolveExpression(e.Index, opts);
          if (!UnifyTypes(e.Index.Type, elementType)) {
            Error(e.Index, "multiset update requires domain element to be of type {0} (got {1})", elementType, e.Index.Type);
          }
          ResolveExpression(e.Value, opts);
          if (!UnifyTypes(e.Value.Type, new OperationTypeProxy(true, false, false, false, false))) {
            Error(e.Value, "multiset update requires integer-based numeric value (got {0})", e.Value.Type);
          }
          expr.Type = e.Seq.Type;

        } else if (e.Seq.Type.IsDatatype) {
          var dt = e.Seq.Type.AsDatatype;

          if (!(e.Index is NameSegment|| (e.Index is LiteralExpr && ((LiteralExpr)e.Index).Value is BigInteger))) {
            Error(expr, "datatype updates must be to datatype destructors");
          } else {
            string destructor_str = null;

            if (e.Index is NameSegment) {
              var seg = (NameSegment)e.Index;
              destructor_str = seg.Name;
            } else {
              Contract.Assert(e.Index is LiteralExpr && ((LiteralExpr)e.Index).Value is BigInteger);
              destructor_str = ((LiteralExpr)e.Index).tok.val;  // note, take the string of digits, not the parsed integer
            }

            if (destructor_str != null) {
              MemberDecl member;
              if (!datatypeMembers[dt].TryGetValue(destructor_str, out member)) {
                Error(expr, "member {0} does not exist in datatype {1}", destructor_str, dt.Name);
              } else {
                // Rewrite an update of the form "dt[dtor := E]" to be "let d' := dt in dtCtr(E, d'.dtor2, d'.dtor3,...)"
                // Wrapping it in a let expr avoids exponential growth in the size of the expression

                // Create a unique name for d', the variable we introduce in the let expression
                string tmpName = FreshTempVarName("dt_update_tmp#", opts.codeContext);
                IdentifierExpr tmpVarIdExpr = new IdentifierExpr(e.Seq.tok, tmpName);
                BoundVar tmpVarBv = new BoundVar(e.Seq.tok, tmpName, e.Seq.Type);

                DatatypeDestructor destructor = (DatatypeDestructor)member;
                DatatypeCtor ctor = destructor.EnclosingCtor;

                // Build the arguments to the datatype constructor, using the updated value in the appropriate slot
                List<Expression> ctor_args = new List<Expression>();
                foreach (Formal d in ctor.Formals) {
                  if (d == destructor.CorrespondingFormal) {
                    ctor_args.Add(e.Value);
                  } else {
                    ctor_args.Add(new ExprDotName(expr.tok, tmpVarIdExpr, d.Name, null));
                  }
                }

                DatatypeValue ctor_call = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, ctor.Name, ctor_args);

                CasePattern tmpVarPat = new CasePattern(e.Seq.tok, tmpVarBv);
                LetExpr let = new LetExpr(e.Seq.tok, new List<CasePattern>() { tmpVarPat }, new List<Expression>() { e.Seq }, ctor_call, true);

                ResolveExpression(let, opts);
                e.ResolvedUpdateExpr = let;

                expr.Type = e.Seq.Type;
              }
            }
          }
        } else {
          Error(expr, "update requires a sequence, map, or datatype (got {0})", e.Seq.Type);
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, opts);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, opts);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, opts);
        }
        var fnType = e.Function.Type.AsArrowType;
        if (fnType == null) {
          Error(e.tok, "non-function expression (of type {0}) is called with parameters", e.Function.Type);
        } else if (fnType.Arity != e.Args.Count) {
          Error(e.tok, "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", fnType, fnType.Arity, e.Args.Count);
        } else {
          for (var i = 0; i < fnType.Arity; i++) {
            if (!UnifyTypes(fnType.Args[i], e.Args[i].Type)) {
              Error(e.Args[i].tok, "type mismatch for argument {0} (function expects {1}, got {2})", i, fnType.Args[i], e.Args[i].Type);
            }
          }
        }
        expr.Type = fnType == null ? new InferredTypeProxy() : fnType.Result;

      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        if (!opts.twoState) {
          Error(expr, "old expressions are not allowed in this context");
        }
        ResolveExpression(e.E, opts);
        expr.Type = e.E.Type;

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, opts);
        if (!UnifyTypes(e.E.Type, new SetType(new InferredTypeProxy())) && !UnifyTypes(e.E.Type, new SeqType(new InferredTypeProxy()))) {
          Error(e.tok, "can only form a multiset from a seq or set.");
        }
        expr.Type = new MultiSetType(e.E.Type.AsCollectionType.Arg);

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, opts);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            if (!UnifyTypes(e.E.Type, Type.Bool)) {
              Error(expr, "logical negation expects a boolean argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Bool;
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            if (!UnifyTypes(e.E.Type, new CollectionTypeProxy(new InferredTypeProxy(), false))) {
              Error(expr, "size operator expects a collection argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Int;
            break;
          case UnaryOpExpr.Opcode.Fresh:
            if (!opts.twoState) {
              Error(expr, "fresh expressions are not allowed in this context");
            }
            // the type of e.E must be either an object or a collection of objects
            Type t = e.E.Type.NormalizeExpand();
            Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
            if (t is CollectionType) {
              t = ((CollectionType)t).Arg.NormalizeExpand();
            }
            if (t is ObjectType) {
              // fine
            } else if (UserDefinedType.DenotesClass(t) != null) {
              // fine
            } else if (t.IsDatatype) {
              // fine, treat this as the datatype itself.
            } else {
              Error(expr, "the argument of a fresh expression must denote an object or a collection of objects (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Bool;
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveType(e.tok, e.ToType, opts.codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.DontInfer), null);
        ResolveExpression(e.E, opts);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Int)) {
          if (!UnifyTypes(e.E.Type, new OperationTypeProxy(true, true, false, false, false))) {
            Error(expr, "type conversion to an int-based type is allowed only from numeric types (got {0})", e.E.Type);
          }
        } else if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          if (!UnifyTypes(e.E.Type, new OperationTypeProxy(true, true, false, false, false))) {
            Error(expr, "type conversion to a real-based type is allowed only from numeric types (got {0})", e.E.Type);
          }
        } else {
          Error(expr, "type conversions are not supported to this type (got {0})", e.ToType);
        }
        e.Type = e.ToType;

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, opts);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, opts);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
          case BinaryExpr.Opcode.Exp:
          case BinaryExpr.Opcode.And:
          case BinaryExpr.Opcode.Or:
            if (!UnifyTypes(e.E0.Type, Type.Bool)) {
              Error(expr, "first argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, Type.Bool)) {
              Error(expr, "second argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
            // We will both check for comparability and attempt to unify the types, and we do them in this order so that
            // the compatibility check is not influenced by the unification.
            var areComparable = ComparableTypes(e.E0.Type, e.E1.Type);
            var unificationSuccess = UnifyTypes(e.E0.Type, e.E1.Type);
            if (areComparable) {
              // The expression is legal.  For example, we may have received two equal types, or we have have gotten types like
              // array<T> and array<U> where T is a type parameter and U is some type.
              // Still, we're still happy that we did the type unification to assign type proxies as needed.
            } else if (unificationSuccess) {
              // The expression is legal.  This can happen if one of the types contains a type proxy.  For example, if the
              // first type is array<T> and the second type is a proxy, then the compatibility check will return false but
              // unification will succeed.
            } else {
              // The types are not comparable and do not unify.  It's time for an error message.
              Error(expr, "arguments must have the same type (got {0} and {1})", e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Disjoint:
            // TODO: the error messages are backwards from what (ideally) they should be. this is necessary because UnifyTypes can't backtrack.
            if (!UnifyTypes(e.E0.Type, e.E1.Type)) {
              Error(expr, "arguments must have the same type (got {0} and {1})", e.E0.Type, e.E1.Type);
            }
            if (!UnifyTypes(e.E0.Type, new SetType(new InferredTypeProxy())) &&
                !UnifyTypes(e.E0.Type, new MultiSetType(new InferredTypeProxy())) &&
                !UnifyTypes(e.E0.Type, new MapType(true, new InferredTypeProxy(), new InferredTypeProxy()))) {
              Error(expr, "arguments must be of a [multi]set or map type (got {0})", e.E0.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le:
          case BinaryExpr.Opcode.Add: {
              if (e.Op == BinaryExpr.Opcode.Lt && (e.E0.Type.NormalizeExpand().IsIndDatatype || e.E0.Type.IsTypeParameter)) {
                if (UnifyTypes(e.E1.Type, new DatatypeProxy(false, false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                expr.Type = Type.Bool;
              } else if (e.Op == BinaryExpr.Opcode.Lt && e.E1.Type.NormalizeExpand().IsIndDatatype) {
                if (UnifyTypes(e.E0.Type, new DatatypeProxy(false, true))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E0.Type);
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                bool isComparison = e.Op != BinaryExpr.Opcode.Add;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true, true, isComparison, true, true))) {
                  Error(expr, "arguments to {0} must be of a numeric type{2} or a collection type (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type,
                    isComparison ? ", char," : "");
                  err = true;
                }
                if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
                  Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
                  err = true;
                }
                if (isComparison) {
                  expr.Type = Type.Bool;
                } else if (!err) {
                  expr.Type = e.E0.Type;
                }
              }
            }
            break;

          case BinaryExpr.Opcode.Sub:
          case BinaryExpr.Opcode.Mul:
          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge: {
              if (e.Op == BinaryExpr.Opcode.Gt && e.E0.Type.NormalizeExpand().IsIndDatatype) {
                if (UnifyTypes(e.E1.Type, new DatatypeProxy(false, true))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                expr.Type = Type.Bool;
              } else if (e.Op == BinaryExpr.Opcode.Gt && (e.E1.Type.NormalizeExpand().IsIndDatatype || e.E1.Type.IsTypeParameter)) {
                if (UnifyTypes(e.E0.Type, new DatatypeProxy(false, false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E0.Type);
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                bool isComparison = e.Op == BinaryExpr.Opcode.Gt || e.Op == BinaryExpr.Opcode.Ge;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true, true, isComparison, false, true))) {
                  Error(expr, "arguments to {0} must be of a numeric type{2} or a set type (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type,
                    isComparison ? ", char, " : "");
                  err = true;
                }
                if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
                  Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
                  err = true;
                }
                if (isComparison) {
                  expr.Type = Type.Bool;
                } else if (!err) {
                  expr.Type = e.E0.Type;
                }
              }
            }
            break;

          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            if (!UnifyTypes(e.E1.Type, new CollectionTypeProxy(e.E0.Type, true))) {
              Error(expr, "second argument to \"{0}\" must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Div:
            if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true, true, false, false, false))) {
              Error(expr, "first argument to {0} must be of numeric type (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
              Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
            }
            expr.Type = e.E0.Type;
            break;

          case BinaryExpr.Opcode.Mod:
            if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true, false, false, false, false))) {
              Error(expr, "first argument to {0} must be of type int (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
              Error(expr, "second argument to {0} must be of type int (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
            }
            expr.Type = e.E0.Type;
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
        }
        // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
        // setting e.ResolvedOp until inside CheckTypeInference.

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, opts);
        ResolveExpression(e.E1, opts);
        ResolveExpression(e.E2, opts);
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            if (!UnifyTypes(e.E0.Type, Type.Int)) {
              Error(e.E0, "prefix-equality limit argument must be an integer expression (got {0})", e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, new DatatypeProxy(true))) {
              Error(expr, "arguments to prefix equality must be codatatypes (instead of {0})", e.E1.Type);
            }
            if (!UnifyTypes(e.E1.Type, e.E2.Type)) {
              Error(expr, "arguments must have the same type (got {0} and {1})", e.E1.Type, e.E2.Type);
            }
            expr.Type = Type.Bool;
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            Error(expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType, opts.codeContext);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            var c = 0;
            foreach (var v in lhs.Vars) {
              if (!scope.Push(v.Name, v)) {
                Error(v, "Duplicate let-variable name: {0}", v.Name);
              }
              c++;
            }
            if (c == 0) {
              // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
              Error(lhs.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
            }
            i++;
          }
        } else {
          // let-such-that expression
          if (e.RHSs.Count != 1) {
            Error(expr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
          }
          // the bound variables are in scope in the RHS of a let-such-that expression
          scope.PushMarker();
          foreach (var lhs in e.LHSs) {
            Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
            var v = lhs.Var;
            if (!scope.Push(v.Name, v)) {
              Error(v, "Duplicate let-variable name: {0}", v.Name);
            }
            ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
            if (!UnifyTypes(rhs.Type, Type.Bool)) {
              Error(rhs.tok, "type of RHS of let-such-that expression must be boolean (got {0})", rhs.Type);
            }
          }
          if (!opts.DontCareAboutCompilation && !e.BoundVars.All(bv => bv.IsGhost)) {
            needFiniteBoundsChecks_LetSuchThatExpr.Add(e);
          }
        }
        ResolveExpression(e.Body, opts);
        ResolveAttributes(e.Attributes, new ResolveOpts(opts, true));
        scope.PopMarker();
        expr.Type = e.Body.Type;

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        ResolveExpression(e.Body, opts);
        if (e.Contract != null) ResolveExpression(e.Contract, opts);
        e.Type = e.Body.Type;
      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        int prevErrorCount = ErrorCount;
        bool _val = true;
        bool typeQuantifier = Attributes.ContainsBool(e.Attributes, "typeQuantifier", ref _val) && _val;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(e.TypeArgs, true, e);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          var option = typeQuantifier ? new ResolveTypeOption(e) : new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies);
          ResolveType(v.tok, v.Type, opts.codeContext, option, typeQuantifier ? e.TypeArgs : null);
        }
        if (e.TypeArgs.Count > 0 && !typeQuantifier) {
          Error(expr, "a quantifier cannot quantify over types. Possible fix: use the experimental attribute :typeQuantifier");
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, new ResolveOpts(opts, true));
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Range.Type, Type.Bool)) {
            Error(expr, "range of quantifier must be of type bool (instead got {0})", e.Range.Type);
          }
        }
        ResolveExpression(e.Term, new ResolveOpts(opts, true));
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Term.Type, Type.Bool)) {
          Error(expr, "body of quantifier must be of type bool (instead got {0})", e.Term.Type);
        }
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e.Attributes, new ResolveOpts(opts, true));
        scope.PopMarker();
        allTypeParameters.PopMarker();
        expr.Type = Type.Bool;

        if (prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.LogicalBody());  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.LogicalBody(), e is ExistsExpr, false, missingBounds);
          if (missingBounds.Count != 0) {
            // Report errors here about quantifications that depend on the allocation state.
            var mb = missingBounds;
            if (opts.codeContext is Function) {
              mb = new List<BoundVar>();  // (who cares if we allocate another array; this happens only in the case of a resolution error anyhow)
              foreach (var bv in missingBounds) {
                if (bv.Type.IsRefType) {
                  Error(expr, "a quantifier involved in a function definition is not allowed to depend on the set of allocated references; Dafny's heuristics can't figure out a bound for the values of '{0}'", bv.Name);
                } else {
                  mb.Add(bv);
                }
              }
            }
            if (mb.Count != 0) {
              e.MissingBounds = mb;
            }
          }
        }

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(e.Range, opts);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Range.Type, Type.Bool)) {
          Error(expr, "range of comprehension must be of type bool (instead got {0})", e.Range.Type);
        }
        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, new ResolveOpts(opts, true));
        scope.PopMarker();
        expr.Type = new SetType(e.Term.Type);

        if (opts.DontCareAboutCompilation && (e.Term.Type.IsRefType || e.Term.Type.IsBoolType) || e.Term.Type.IsCharType) {
          // ok, term type is finite and we're in a ghost context
        } else {
          needFiniteBoundsChecks_SetComprehension.Add(e);
        }

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        if (e.BoundVars.Count != 1) {
          Error(e.tok, "a map comprehension must have exactly one bound variable.");
        }
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(e.Range, opts);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Range.Type, Type.Bool)) {
          Error(expr, "range of comprehension must be of type bool (instead got {0})", e.Range.Type);
        }
        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, new ResolveOpts(opts, true));
        scope.PopMarker();
        expr.Type = new MapType(e.Finite, e.BoundVars[0].Type, e.Term.Type);

        if (prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.Range);  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            e.MissingBounds = missingBounds;
            if (e.Finite) {
              foreach (var bv in e.MissingBounds) {
                Error(expr, "a map comprehension must produce a finite domain, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
              }
            }
          }
        }
      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, opts);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Range.Type, Type.Bool)) {
            Error(expr, "Precondition must be boolean (got {0})", e.Range.Type);
          }
        }

        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, true, false, opts.codeContext);
        }

        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);
        scope.PopMarker();
        expr.Type = new ArrowType(e.tok, Util.Map(e.BoundVars, v => v.Type), e.Body.Type, builtIns.SystemModule);
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(new ObjectType());
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = ErrorCount;
        ResolveStatement(e.S, true, opts.codeContext);
        if (ErrorCount == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method.Mod.Expressions.Count != 0) {
              Error(call, "calls to methods with side-effects are not allowed inside a statement expression");
            }
          }
        }
        ResolveExpression(e.E, opts);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, opts);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, opts);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, opts);
        Contract.Assert(e.Els.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Test.Type, Type.Bool)) {
          Error(expr, "guard condition in if-then-else expression must be a boolean (instead got {0})", e.Test.Type);
        }
        if (UnifyTypes(e.Thn.Type, e.Els.Type)) {
          expr.Type = e.Thn.Type;
        } else {
          Error(expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);
        }

      } else if (expr is MatchExpr) {
        var me = (MatchExpr)expr;
        ResolveExpression(me.Source, opts);
        Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        if (me.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)me.Source.Type.NormalizeExpand();
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
        var subst = new Dictionary<TypeParameter, Type>();
        Dictionary<string, DatatypeCtor> ctors;
        if (dtd == null) {
          Error(me.Source, "the type of the match source expression must be a datatype (instead found {0})", me.Source.Type);
          ctors = null;
        } else {
          Contract.Assert(sourceType != null);  // dtd and sourceType are set together above
          ctors = datatypeCtors[dtd];
          Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage

          // build the type-parameter substitution map for this use of the datatype
          for (int i = 0; i < dtd.TypeArgs.Count; i++) {
            subst.Add(dtd.TypeArgs[i], sourceType.TypeArgs[i]);
          }
        }

        ISet<string> memberNamesUsed = new HashSet<string>();
        expr.Type = new InferredTypeProxy();
        foreach (MatchCaseExpr mc in me.Cases) {
          DatatypeCtor ctor = null;
          if (ctors != null) {
            Contract.Assert(dtd != null);
            if (!ctors.TryGetValue(mc.Id, out ctor)) {
              Error(mc.tok, "member {0} does not exist in datatype {1}", mc.Id, dtd.Name);
            } else {
              Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
              mc.Ctor = ctor;
              if (ctor.Formals.Count != mc.Arguments.Count) {
                Error(mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", mc.Id, mc.Arguments.Count, ctor.Formals.Count);
              }
              if (memberNamesUsed.Contains(mc.Id)) {
                Error(mc.tok, "member {0} appears in more than one case", mc.Id);
              } else {
                memberNamesUsed.Add(mc.Id);  // add mc.Id to the set of names used
              }
            }
          }
          scope.PushMarker();
          int i = 0;
          foreach (BoundVar v in mc.Arguments) {
            if (!scope.Push(v.Name, v)) {
              Error(v, "Duplicate parameter name: {0}", v.Name);
            }
            ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (ctor != null && i < ctor.Formals.Count) {
              Formal formal = ctor.Formals[i];
              Type st = SubstType(formal.Type, subst);
              if (!UnifyTypes(v.Type, st)) {
                Error(expr, "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", v.Type, st);
              }
              v.IsGhost = formal.IsGhost;
            }
            i++;
          }
          ResolveExpression(mc.Body, opts);
          Contract.Assert(mc.Body.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(expr.Type, mc.Body.Type)) {
            Error(mc.Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", mc.Body.Type, expr.Type);
          }
          scope.PopMarker();
        }
        if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
          // We could complain about the syntactic omission of constructors:
          //   Error(expr, "match expression does not cover all constructors");
          // but instead we let the verifier do a semantic check.
          // So, for now, record the missing constructors:
          foreach (var ctr in dtd.Ctors) {
            if (!memberNamesUsed.Contains(ctr.Name)) {
              me.MissingCases.Add(ctr);
            }
          }
          Contract.Assert(memberNamesUsed.Count + me.MissingCases.Count == dtd.Ctors.Count);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = new InferredTypeProxy();
      }
    }

    void ResolveCasePattern(CasePattern pat, Type sourceType, ICodeContext context) {
      Contract.Requires(pat != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(context != null);

      DatatypeDecl dtd = null;
      UserDefinedType udt = null;
      if (sourceType.IsDatatype) {
        udt = (UserDefinedType)sourceType.NormalizeExpand();
        dtd = (DatatypeDecl)udt.ResolvedClass;
      }
      // Find the constructor in the given datatype
      // If what was parsed was just an identifier, we will interpret it as a datatype constructor, if possible
      DatatypeCtor ctor = null;
      if (pat.Var == null || (pat.Var != null && pat.Var.Type is TypeProxy && dtd != null)) {
        if (datatypeCtors[dtd].TryGetValue(pat.Id, out ctor)) {
          pat.Ctor = ctor;
          pat.Var = null;
        }
      }

      if (pat.Var != null) {
        // this is a simple resolution
        var v = pat.Var;
        ResolveType(v.tok, v.Type, context, ResolveTypeOptionEnum.InferTypeProxies, null);
        if (!UnifyTypes(v.Type, sourceType)) {
          Error(v.tok, "type of corresponding source/RHS ({0}) does not match type of bound variable ({1})", sourceType, v.Type);
        }
        pat.AssembleExpr(null);
      } else if (dtd == null) {
        Error(pat.tok, "to use a pattern, the type of the source/RHS expression must be a datatype (instead found {0})", sourceType);
      } else if (ctor == null) {
        Error(pat.tok, "constructor {0} does not exist in datatype {1}", pat.Id, dtd.Name);
      } else {
        var argCount = pat.Arguments == null ? 0 : pat.Arguments.Count;
        if (ctor.Formals.Count != argCount) {
          Error(pat.tok, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, argCount, ctor.Formals.Count);
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == udt.TypeArgs.Count);  // follows from the type previously having been successfully resolved
        var subst = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < dtd.TypeArgs.Count; i++) {
          subst.Add(dtd.TypeArgs[i], udt.TypeArgs[i]);
        }
        // recursively call ResolveCasePattern on each of the arguments
        var j = 0;
        foreach (var arg in pat.Arguments) {
          if (j < ctor.Formals.Count) {
            var formal = ctor.Formals[j];
            Type st = SubstType(formal.Type, subst);
            ResolveCasePattern(arg, st, context);
          }
          j++;
        }
        if (j == ctor.Formals.Count) {
          pat.AssembleExpr(udt.TypeArgs);
        }
      }
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Local variable, parameter, or bound variable.
    ///     (Language design note:  If this clashes with something of interest, one can always rename the local variable locally.)
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. If isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module (if two constructors have the same name, an error message is produced here)
    ///     (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///  3. Member of the enclosing module (type name or the name of a module)
    ///  4. Static function or method in the enclosing module or its imports
    ///  
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="opts"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<Expression> args, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (ty.IsSubrangeType) {
            Error(expr.tok, "sorry, cannot instantiate type parameter with a subrange type");
          }
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 0:
      IVariable v;
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 4:
      MemberDecl member = null;
      // For 2:
      Tuple<DatatypeCtor, bool> pair;
      // For 3:
      TopLevelDecl decl;

      v = scope.Find(expr.Name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          Error(expr.tok, "variable '{0}' does not take any type parameters", expr.Name);
        }
        var rr = new IdentifierExpr(expr.tok, expr.Name);
        rr.Var = v; rr.Type = v.Type;
        r = rr;
      } else if (currentClass != null && classMembers.TryGetValue(currentClass, out members) && members.TryGetValue(expr.Name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
        } else {
          if (!scope.AllowInstance) {
            Error(expr.tok, "'this' is not allowed in a 'static' context");
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, (ClassDecl)member.EnclosingClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
      } else if (isLastNameSegment && moduleInfo.Ctors.TryGetValue(expr.Name, out pair)) {
        // ----- 2. datatype constructor
        if (pair.Item2) {
          // there is more than one constructor with this name
          Error(expr.tok, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", expr.Name, pair.Item1.EnclosingDatatype.Name);
        } else {
          if (expr.OptTypeArguments != null) {
            Error(expr.tok, "datatype constructor does not take any type parameters ('{0}')", expr.Name);
          }
          var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, expr.Name, args ?? new List<Expression>());
          ResolveDatatypeValue(opts, rr, pair.Item1.EnclosingDatatype);
          if (args == null) {
            r = rr;
          } else {
            r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
            rWithArgs = rr;
          }
        }
      } else if (moduleInfo.TopLevels.TryGetValue(expr.Name, out decl)) {
        // ----- 3. Member of the enclosing module
        if (ReallyAmbiguousTopLevelDecl(ref decl)) {
          Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ((AmbiguousTopLevelDecl)decl).ModuleNames());
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          r = CreateResolver_IdentifierExpr(expr.tok, expr.Name, expr.OptTypeArguments, decl);
        }

      } else if (moduleInfo.StaticMembers.TryGetValue(expr.Name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (ReallyAmbiguousThing(ref member)) {
          Error(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ((AmbiguousMemberDecl)member).ModuleNames());
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
        }

      } else {
        // ----- None of the above
        Error(expr.tok, "unresolved identifier: {0}", expr.Name);
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Type parameter
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. Member of the enclosing module (type name or the name of a module)
    ///  3. Static function or method in the enclosing module or its imports
    ///  
    /// Note: 1 and 3 are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    void ResolveNameSegment_Type(NameSegment expr, ResolveOpts opts, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, option, defaultTypeArguments);
          if (ty.IsSubrangeType) {
            Error(expr.tok, "sorry, cannot instantiate type parameter with a subrange type");
          }
        }
      }

      Expression r = null;  // the resolved expression, if successful

      // For 0:
      TypeParameter tp;
#if ASYNC_TASK_TYPES
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 3:
      MemberDecl member = null;
#endif
      // For 2:
      TopLevelDecl decl;

      tp = allTypeParameters.Find(expr.Name);
      if (tp != null) {
        // ----- 0. type parameter
        if (expr.OptTypeArguments == null) {
          r = new Resolver_IdentifierExpr(expr.tok, tp);
        } else {
          Error(expr.tok, "Type parameter expects no type arguments: {0}", expr.Name);
        }
#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (currentClass != null && classMembers.TryGetValue(currentClass, out members) && members.TryGetValue(expr.Name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
        } else {
          if (!scope.AllowInstance) {
            Error(expr.tok, "'this' is not allowed in a 'static' context");
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, (ClassDecl)member.EnclosingClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
#endif
      } else if (moduleInfo.TopLevels.TryGetValue(expr.Name, out decl)) {
        // ----- 2. Member of the enclosing module
        if (ReallyAmbiguousTopLevelDecl(ref decl)) {
          Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ((AmbiguousTopLevelDecl)decl).ModuleNames());
        } else {
          // We have found a module name or a type name, neither of which is a type expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into a type expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          r = CreateResolver_IdentifierExpr(expr.tok, expr.Name, expr.OptTypeArguments, decl);
        }

#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (moduleInfo.StaticMembers.TryGetValue(expr.Name, out member)) {
        // ----- 3. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (ReallyAmbiguousThing(ref member)) {
          Error(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ((AmbiguousMemberDecl)member).ModuleNames());
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
        }
#endif
      } else if (option.Opt == ResolveTypeOptionEnum.AllowPrefixExtend && expr.OptTypeArguments == null) {
        // it woulc plausibly be a type parameter, but isn't; we will declare it automatically
        tp = new TypeParameter(expr.tok, expr.Name, defaultTypeArguments.Count, option.Parent);
        defaultTypeArguments.Add(tp);
        r = new Resolver_IdentifierExpr(expr.tok, tp);
        allTypeParameters.Push(expr.Name, tp);
      } else {
        // ----- None of the above
        Error(expr.tok, "Undeclared top-level type or type parameter: {0} (did you forget to qualify a name?)", expr.Name);
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
    }

    Resolver_IdentifierExpr CreateResolver_IdentifierExpr(IToken tok, string name, List<Type> optTypeArguments, TopLevelDecl decl) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Resolver_IdentifierExpr>() != null);
      var n = optTypeArguments == null ? 0 : optTypeArguments.Count;
      if (optTypeArguments != null) {
        // type arguments were supplied; they must be equal in number to those expected
        if (n != decl.TypeArgs.Count) {
          Error(tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", n, decl.TypeArgs.Count, decl.WhatKind, name);
        }
      }
      List<Type> tpArgs = new List<Type>();
      for (int i = 0; i < decl.TypeArgs.Count; i++) {
        tpArgs.Add(i < n ? optTypeArguments[i] : new InferredTypeProxy());
      }
      return new Resolver_IdentifierExpr(tok, decl, tpArgs);
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. If isLastNameSegment:
    ///         Unambiguous constructor name of a datatype in module M (if two constructors have the same name, an error message is produced here)
    ///         (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///      1. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      2. Static function or method of M._default
    ///    (Note that in contrast to ResolveNameSegment, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      3. Look up id as a member of that type
    ///  * If E denotes an expression:
    ///      4. Let T be the type of E.  Look up id in T.
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the ExprDotName is not directly enclosed in another ExprDotName expression.</param>
    /// <param name="args">If the ExprDotName is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="opts"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a Resolver_MethodCall.</param>
    Expression ResolveDotSuffix(ExprDotName expr, bool isLastNameSegment, List<Expression> args, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, opts, false);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, null, opts, false);
      } else {
        ResolveExpression(expr.Lhs, opts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (ty.IsSubrangeType) {
            Error(expr.tok, "sorry, cannot instantiate type parameter with a subrange type");
          }
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"
      MemberDecl member = null;

      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).Signature;
        sig = GetSignature(sig);
        // For 0:
        Tuple<DatatypeCtor, bool> pair;
        // For 1:
        TopLevelDecl decl;

        if (isLastNameSegment && moduleInfo.Ctors.TryGetValue(expr.SuffixName, out pair)) {
          // ----- 0. datatype constructor
          if (pair.Item2) {
            // there is more than one constructor with this name
            Error(expr.tok, "the name '{0}' denotes a datatype constructor in module {2}, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", expr.SuffixName, pair.Item1.EnclosingDatatype.Name, ((ModuleDecl)ri.Decl).Name);
          } else {
            if (expr.OptTypeArguments != null) {
              Error(expr.tok, "datatype constructor does not take any type parameters ('{0}')", expr.SuffixName);
            }
            var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, expr.SuffixName, args ?? new List<Expression>());
            ResolveExpression(rr, opts);
            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        } else if (sig.TopLevels.TryGetValue(expr.SuffixName, out decl)) {
          // ----- 1. Member of the specified module
          if (ReallyAmbiguousTopLevelDecl(ref decl)) {
            Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ((AmbiguousTopLevelDecl)decl).ModuleNames());
          } else {
            // We have found a module name or a type name, neither of which is an expression. However, the ExprDotName we're
            // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
            // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            r = CreateResolver_IdentifierExpr(expr.tok, expr.SuffixName, expr.OptTypeArguments, decl);
          }
        } else if (sig.StaticMembers.TryGetValue(expr.SuffixName, out member)) {
          // ----- 2. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (ReallyAmbiguousThing(ref member)) {
            Error(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ((AmbiguousMemberDecl)member).ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
          }
        } else {
          Error(expr.tok, "unresolved identifier: {0}", expr.SuffixName);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 3. Look up name in type
        Type ty;
        if (ri.TypeParamDecl != null) {
          ty = new UserDefinedType(ri.TypeParamDecl);
        } else {
          // expand any synonyms
          ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        }
        if (ty.IsRefType) {
          // ----- LHS is a class
          var cd = (ClassDecl)((UserDefinedType)ty).ResolvedClass;
          Dictionary<string, MemberDecl> members;
          if (classMembers.TryGetValue(cd, out members) && members.TryGetValue(expr.SuffixName, out member)) {
            if (!member.IsStatic) {
              Error(expr.tok, "accessing member '{0}' requires an instance expression", expr.SuffixName);
              // nevertheless, continue creating an expression that approximates a correct one
            }
            var receiver = new StaticReceiverExpr(expr.tok, ty);
            receiver.Type = ty;
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
          }
        } else if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          Dictionary<string, DatatypeCtor> members;
          DatatypeCtor ctor;
          if (datatypeCtors.TryGetValue(dt, out members) && members.TryGetValue(expr.SuffixName, out ctor)) {
            if (expr.OptTypeArguments != null) {
              Error(expr.tok, "datatype constructor does not take any type parameters ('{0}')", expr.SuffixName);
            }
            var rr = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, expr.SuffixName, args ?? new List<Expression>());
            ResolveDatatypeValue(opts, rr, ctor.EnclosingDatatype);
            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        }
        if (r == null) {
          Error(expr.tok, "member '{0}' does not exist in type '{1}'", expr.SuffixName, ri.TypeParamDecl != null ? ri.TypeParamDecl.Name : ri.Decl.Name);
        }
      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        NonProxyType nptype;
        member = ResolveMember(expr.tok, expr.Lhs.Type, expr.SuffixName, out nptype);
        if (member != null) {
          var receiver = expr.Lhs;
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      1. Static member of M._default denoting an async task type
    ///    (Note that in contrast to ResolveNameSegment_Type, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      2. a. Member of that type denoting an async task type, or:
    ///         b. If allowDanglingDotName:
    ///            Return the type "E" and the given "expr", letting the caller try to make sense of the final dot-name.
    ///      
    /// Note: 1 and 2a are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    ResolveTypeReturn ResolveDotSuffix_Type(ExprDotName expr, ResolveOpts opts, bool allowDanglingDotName, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(expr.Lhs is NameSegment || expr.Lhs is ExprDotName);
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<ResolveTypeReturn>() == null || allowDanglingDotName);

      // resolve the LHS expression
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment_Type((NameSegment)expr.Lhs, opts, option, defaultTypeArguments);
      } else {
        ResolveDotSuffix_Type((ExprDotName)expr.Lhs, opts, false, option, defaultTypeArguments);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, option, defaultTypeArguments);
          if (ty.IsSubrangeType) {
            Error(expr.tok, "sorry, cannot instantiate type parameter with a subrange type");
          }
        }
      }

      Expression r = null;  // the resolved expression, if successful

      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).Signature;
        sig = GetSignature(sig);
        // For 0:
        TopLevelDecl decl;

        if (sig.TopLevels.TryGetValue(expr.SuffixName, out decl)) {
          // ----- 0. Member of the specified module
          if (ReallyAmbiguousTopLevelDecl(ref decl)) {
            Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ((AmbiguousTopLevelDecl)decl).ModuleNames());
          } else {
            // We have found a module name or a type name.  We create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            r = CreateResolver_IdentifierExpr(expr.tok, expr.SuffixName, expr.OptTypeArguments, decl);
          }
#if ASYNC_TASK_TYPES
        } else if (sig.StaticMembers.TryGetValue(expr.SuffixName, out member)) {
          // ----- 1. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (ReallyAmbiguousThing(ref member)) {
            Error(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ((AmbiguousMemberDecl)member).ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
          }
#endif
        } else {
          Error(expr.tok, "module '{0}' does not declare a type '{1}'", ri.Decl.Name, expr.SuffixName);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 2. Look up name in type
        Type ty;
        if (ri.TypeParamDecl != null) {
          ty = new UserDefinedType(ri.TypeParamDecl);
        } else {
          ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs);
        }
        if (allowDanglingDotName && ty.IsRefType) {
          return new ResolveTypeReturn(ty, expr);
        }
        if (r == null) {
          Error(expr.tok, "member '{0}' does not exist in type '{1}' or cannot be part of type name", expr.SuffixName, ri.TypeParamDecl != null ? ri.TypeParamDecl.Name : ri.Decl.Name);
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return null;
    }

    Expression ResolveExprDotCall(IToken tok, Expression receiver, MemberDecl member, List<Type> optTypeArguments, ICodeContext caller, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.WasResolved());
      Contract.Requires(member != null);
      Contract.Requires(caller != null);

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

      // Now, fill in rr.Type.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      Dictionary<TypeParameter, Type> subst;
      var udt = receiver.Type.NormalizeExpand() as UserDefinedType;
      if (udt != null && udt.ResolvedClass != null) {
        subst = TypeSubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
      } else {
        subst = new Dictionary<TypeParameter, Type>();
      }

      if (member is Field) {
        if (optTypeArguments != null) {
          Error(tok, "a field ({0}) does not take any type arguments (got {1})", member.Name, optTypeArguments.Count);
        }
        rr.Type = SubstType(((Field)member).Type, subst);
      } else if (member is Function) {
        var fn = (Function)member;
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != fn.TypeArgs.Count) {
          Error(tok, "function '{0}' expects {1} type arguments (got {2})", member.Name, fn.TypeArgs.Count, suppliedTypeArguments);
        }
        rr.TypeApplication = new List<Type>();
        if (udt != null && udt.ResolvedClass != null) {
          rr.TypeApplication.AddRange(udt.TypeArgs);
        }
        for (int i = 0; i < fn.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication.Add(ta);
          subst.Add(fn.TypeArgs[i], ta);
        }
        rr.Type = new ArrowType(fn.tok, fn.Formals.ConvertAll(f => SubstType(f.Type, subst)), SubstType(fn.ResultType, subst), builtIns.SystemModule);
        AddCallGraphEdge(caller, fn, rr);
      } else {
        // the member is a method
        var m = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given context
          Error(tok, "expression is not allowed to invoke a method ({0})", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != m.TypeArgs.Count) {
          Error(tok, "method '{0}' expects {1} type arguments (got {2})", member.Name, m.TypeArgs.Count, suppliedTypeArguments);
        }
        rr.TypeApplication = new List<Type>();
        if (udt != null && udt.ResolvedClass != null) {
          rr.TypeApplication.AddRange(udt.TypeArgs);
        }
        for (int i = 0; i < m.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication.Add(ta);
        }
        rr.Type = new InferredTypeProxy();  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    class MethodCallInformation
    {
      public readonly IToken Tok;
      public readonly MemberSelectExpr Callee;
      public readonly List<Expression> Args;

      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Tok != null);
        Contract.Invariant(Callee != null);
        Contract.Invariant(Callee.Member is Method);
        Contract.Invariant(cce.NonNullElements(Args));
      }

      public MethodCallInformation(IToken tok, MemberSelectExpr callee, List<Expression> args) {
        Contract.Requires(tok != null);
        Contract.Requires(callee != null);
        Contract.Requires(callee.Member is Method);
        Contract.Requires(cce.NonNullElements(args));
        this.Tok = tok;
        this.Callee = callee;
        this.Args = args;
      }
    }

    MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);
      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = ErrorCount;
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Args, opts, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, true, e.Args, opts, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else {
        ResolveExpression(e.Lhs, opts);
      }
      if (r == null) {
        foreach (var arg in e.Args) {
          ResolveExpression(arg, opts);
        }
        var fnType = e.Lhs.Type.AsArrowType;
        if (fnType == null) {
          var lhs = e.Lhs.Resolved;
          if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
            Error(e.tok, "name of module ({0}) is used as a function", ((Resolver_IdentifierExpr)lhs).Decl.Name);
          } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            // It may be a conversion expression
            var ri = (Resolver_IdentifierExpr)lhs;
            if (ri.TypeParamDecl != null) {
              Error(e.tok, "name of type parameter ({0}) is used as a function", ri.TypeParamDecl.Name);
            } else {
              var decl = ri.Decl;
              var ty = new UserDefinedType(e.tok, decl.Name, decl, ri.TypeArgs);
              if (ty.AsNewtype != null) {
                if (e.Args.Count != 1) {
                  Error(e.tok, "conversion operation to {0} got wrong number of arguments (expected 1, got {1})", decl.Name, e.Args.Count);
                }
                var conversionArg = 1 <= e.Args.Count ? e.Args[0] :
                  ty.IsNumericBased(Type.NumericPersuation.Int) ? LiteralExpr.CreateIntLiteral(e.tok, 0) :
                  LiteralExpr.CreateRealLiteral(e.tok, Basetypes.BigDec.ZERO);
                r = new ConversionExpr(e.tok, conversionArg, ty);
                ResolveExpression(r, opts);
                // resolve the rest of the arguments, if any
                for (int i = 1; i < e.Args.Count; i++) {
                  ResolveExpression(e.Args[i], opts);
                }
              } else {
                Error(e.tok, "name of type ({0}) is used as a function", decl.Name);
              }
            }
          } else {
            if (lhs is MemberSelectExpr && ((MemberSelectExpr)lhs).Member is Method) {
              var mse = (MemberSelectExpr)lhs;
              if (allowMethodCall) {
                var cRhs = new MethodCallInformation(e.tok, mse, e.Args);
                return cRhs;
              } else {
                Error(e.tok, "method call is not allowed to be used in an expression context ({0})", mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              Error(e.tok, "non-function expression (of type {0}) is called with parameters", e.Lhs.Type);
            }
          }
        } else {
          var mse = e.Lhs is NameSegment || e.Lhs is ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse == null ? null : mse.Member as Function;
          if (fnType.Arity != e.Args.Count) {
            var what = callee != null ? string.Format("function '{0}'", callee.Name) : string.Format("function type '{0}'", fnType);
            Error(e.tok, "wrong number of arguments to function application ({0} expects {1}, got {2})", what, fnType.Arity, e.Args.Count);
          } else {
            for (var i = 0; i < fnType.Arity; i++) {
              if (!UnifyTypes(fnType.Args[i], e.Args[i].Type)) {
                Error(e.Args[i].tok, "type mismatch for argument {0} (function expects {1}, got {2})", i, fnType.Args[i], e.Args[i].Type);
              }
            }
            if (errorCount != ErrorCount) {
              // no nothing else; error has been reported
            } else if (callee != null) {
              // produce a FunctionCallExpr instead of an ApplyExpr(MemberSelectExpr)
              var rr = new FunctionCallExpr(e.Lhs.tok, callee.Name, mse.Obj, e.tok, e.Args);
              // resolve it here:
              rr.Function = callee;
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Formals.Count == rr.Args.Count);  // this should have been checked already
              // build the type substitution map
              rr.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
              Contract.Assert(mse.TypeApplication.Count == callee.EnclosingClass.TypeArgs.Count + callee.TypeArgs.Count);
              for (int i = 0; i < callee.EnclosingClass.TypeArgs.Count; i++) {
                rr.TypeArgumentSubstitutions.Add(callee.EnclosingClass.TypeArgs[i], mse.TypeApplication[i]);
              }
              for (int i = 0; i < callee.TypeArgs.Count; i++) {
                rr.TypeArgumentSubstitutions.Add(callee.TypeArgs[i], mse.TypeApplication[callee.EnclosingClass.TypeArgs.Count + i]);
              }
              // type check the arguments
              for (int i = 0; i < callee.Formals.Count; i++) {
                Expression farg = rr.Args[i];
                ResolveExpression(farg, opts);
                Contract.Assert(farg.Type != null);  // follows from postcondition of ResolveExpression
                Type s = SubstType(callee.Formals[i].Type, rr.TypeArgumentSubstitutions);
                if (!UnifyTypes(farg.Type, s)) {
                  Error(rr, "incorrect type of function argument {0} (expected {1}, got {2})", i, s, farg.Type);
                }
              }
              rr.Type = SubstType(callee.ResultType, rr.TypeArgumentSubstitutions);
              // further bookkeeping
              if (callee is CoPredicate) {
                ((CoPredicate)callee).Uses.Add(rr);
              }
              AddCallGraphEdge(opts.codeContext, callee, rr);
              r = rr;
            } else {
              r = new ApplyExpr(e.Lhs.tok, e.Lhs, e.Args);
              r.Type = fnType.Result;
            }
          }
        }
      }
      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        e.Type = new InferredTypeProxy();
      } else {
        e.ResolvedExpression = r;
        e.Type = r.Type;
      }
      return null;
    }

    private void ResolveDatatypeValue(ResolveOpts opts, DatatypeValue dtv, DatatypeDecl dt) {
      // this resolution is a little special, in that the syntax shows only the base name, not its instantiation (which is inferred)
      List<Type> gt = new List<Type>(dt.TypeArgs.Count);
      Dictionary<TypeParameter, Type> subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < dt.TypeArgs.Count; i++) {
        Type t = new InferredTypeProxy();
        gt.Add(t);
        dtv.InferredTypeArgs.Add(t);
        subst.Add(dt.TypeArgs[i], t);
      }
      // Construct a resolved type directly, as we know the declaration is dt.
      dtv.Type = new UserDefinedType(dtv.tok, dt.Name, dt, gt);

      DatatypeCtor ctor;
      if (!datatypeCtors[dt].TryGetValue(dtv.MemberName, out ctor)) {
        Error(dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
      } else {
        Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
        if (ctor.Formals.Count != dtv.Arguments.Count) {
          Error(dtv.tok, "wrong number of arguments to datatype constructor {0} (found {1}, expected {2})", ctor.Name, dtv.Arguments.Count, ctor.Formals.Count);
        }
      }
      int j = 0;
      foreach (Expression arg in dtv.Arguments) {
        Formal formal = ctor != null && j < ctor.Formals.Count ? ctor.Formals[j] : null;
        ResolveExpression(arg, opts);
        Contract.Assert(arg.Type != null);  // follows from postcondition of ResolveExpression
        if (formal != null) {
          Type st = SubstType(formal.Type, subst);
          if (!UnifyTypes(arg.Type, st)) {
            Error(arg.tok, "incorrect type of datatype constructor argument (found {0}, expected {1})", arg.Type, st);
          }
        }
        j++;
      }
    }

    private bool ComparableTypes(Type A, Type B) {
      // If we know that both A and B denote classes and they denote the same class,
      // then we will say the types are comparable (for the purpose of the == and !=
      // opeators) if it isn't blatantly impossible to instantiate the type parameters
      // of the enclosing context so that A and B are exactly the same type.
      var a = A.NormalizeExpand() as UserDefinedType;
      var b = B.NormalizeExpand() as UserDefinedType;
      if (a != null && b != null) {
        if (a is ArrowType || b is ArrowType) {
          return false;
        }
        var acl = a.ResolvedClass;
        var bcl = b.ResolvedClass;
        if (acl is ClassDecl && bcl is ClassDecl && acl == bcl) {
          for (int i = 0; i < acl.TypeArgs.Count; i++) {
            if (!a.TypeArgs[i].PossiblyEquals(b.TypeArgs[i])) {
              return false;
            }
          }
          // all parameters could be the same
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Generate an error for every non-ghost feature used in "expr".
    /// Requires "expr" to have been successfully resolved.
    /// </summary>
    void CheckIsNonGhost(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (e.Var != null && e.Var.IsGhost) {
          Error(expr, "ghost variables are allowed only in specification contexts");
          return;
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member != null && e.Member.IsGhost) {
          Error(expr, "ghost fields are allowed only in specification contexts");
          return;
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function != null) {
          if (e.Function.IsGhost) {
            Error(expr, "function calls are allowed only in specification contexts (consider declaring the function a 'function method')");
            return;
          }
          // function is okay, so check all NON-ghost arguments
          CheckIsNonGhost(e.Receiver);
          for (int i = 0; i < e.Function.Formals.Count; i++) {
            if (!e.Function.Formals[i].IsGhost) {
              CheckIsNonGhost(e.Args[i]);
            }
          }
        }
        return;

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        // check all NON-ghost arguments
        // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
        for (int i = 0; i < e.Arguments.Count; i++) {
          if (!e.Ctor.Formals[i].IsGhost) {
            CheckIsNonGhost(e.Arguments[i]);
          }
        }
        return;

      } else if (expr is OldExpr) {
        Error(expr, "old expressions are allowed only in specification and ghost contexts");
        return;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Fresh) {
          Error(expr, "fresh expressions are allowed only in specification and ghost contexts");
          return;
        }

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // ignore the statement
        CheckIsNonGhost(e.E);
        return;

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        switch (e.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            Error(expr, "rank comparisons are allowed only in specification and ghost contexts");
            return;
          default:
            break;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            Error(expr, "prefix equalities are allowed only in specification and ghost contexts");
            return;
          default:
            break;
        }
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          Contract.Assert(e.LHSs.Count == e.RHSs.Count);
          var i = 0;
          foreach (var ee in e.RHSs) {
            if (!e.LHSs[i].Vars.All(bv => bv.IsGhost)) {
              CheckIsNonGhost(ee);
            }
            i++;
          }
          CheckIsNonGhost(e.Body);
        } else {
          Contract.Assert(e.RHSs.Count == 1);
          var lhsVarsAreAllGhost = e.BoundVars.All(bv => bv.IsGhost);
          if (!lhsVarsAreAllGhost) {
            CheckIsNonGhost(e.RHSs[0]);
          }
          CheckIsNonGhost(e.Body);
        }
        return;
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (e.MissingBounds != null) {
          foreach (var bv in e.MissingBounds) {
            Error(expr, "quantifiers in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
          }
          return;
        }
      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        if (e.MissingBounds != null && !e.Finite) {
          foreach (var bv in e.MissingBounds) {
            Error(expr, "imaps in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
          }
          return;
        }
      } else if (expr is NamedExpr) {
        if (!moduleInfo.IsGhost)
          CheckIsNonGhost(((NamedExpr)expr).Body);
        return;
      } else if (expr is ChainingExpression) {
        // We don't care about the different operators; we only want the operands, so let's get them directly from
        // the chaining expression
        var e = (ChainingExpression)expr;
        e.Operands.ForEach(CheckIsNonGhost);
        return;
      } else if (expr is LambdaExpr) {
        var e = expr as LambdaExpr;
        CheckIsNonGhost(e.Body);
        return;
      }

      foreach (var ee in expr.SubExpressions) {
        CheckIsNonGhost(ee);
      }
    }

    public void ResolveFunctionCallExpr(FunctionCallExpr e, ResolveOpts opts) {
      ResolveReceiver(e.Receiver, opts);
      Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression
      NonProxyType nptype;

      MemberDecl member = ResolveMember(e.tok, e.Receiver.Type, e.Name, out nptype);
#if !NO_WORK_TO_BE_DONE
      UserDefinedType ctype = (UserDefinedType)nptype;
#endif
      if (member == null) {
        // error has already been reported by ResolveMember
      } else if (member is Method) {
        Error(e, "member {0} in type {1} refers to a method, but only functions can be used in this context", e.Name, cce.NonNull(ctype).Name);
      } else if (!(member is Function)) {
        Error(e, "member {0} in type {1} does not refer to a function", e.Name, cce.NonNull(ctype).Name);
      } else {
        Function function = (Function)member;
        e.Function = function;
        if (function is CoPredicate) {
          ((CoPredicate)function).Uses.Add(e);
        }
        if (e.Receiver is StaticReceiverExpr && !function.IsStatic) {
          Error(e, "an instance function must be selected via an object, not just a class name");
        }
        if (function.Formals.Count != e.Args.Count) {
          Error(e, "wrong number of function arguments (got {0}, expected {1})", e.Args.Count, function.Formals.Count);
        } else {
          Contract.Assert(ctype != null);  // follows from postcondition of ResolveMember
          if (!function.IsStatic) {
            if (!scope.AllowInstance && e.Receiver is ThisExpr) {
              // The call really needs an instance, but that instance is given as 'this', which is not
              // available in this context.  In most cases, occurrences of 'this' inside e.Receiver would
              // have been caught in the recursive call to resolve e.Receiver, but not the specific case
              // of e.Receiver being 'this' (explicitly or implicitly), for that case needs to be allowed
              // in the event that a static function calls another static function (and note that we need the
              // type of the receiver in order to find the method, so we could not have made this check
              // earlier).
              Error(e.Receiver, "'this' is not allowed in a 'static' context");
            } else if (e.Receiver is StaticReceiverExpr) {
              Error(e.Receiver, "call to instance function requires an instance");
            }
          }
          // build the type substitution map
          e.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
          for (int i = 0; i < ctype.TypeArgs.Count; i++) {
            e.TypeArgumentSubstitutions.Add(cce.NonNull(ctype.ResolvedClass).TypeArgs[i], ctype.TypeArgs[i]);
          }
          foreach (TypeParameter p in function.TypeArgs) {
            e.TypeArgumentSubstitutions.Add(p, new ParamTypeProxy(p));
          }
          // type check the arguments
          for (int i = 0; i < function.Formals.Count; i++) {
            Expression farg = e.Args[i];
            ResolveExpression(farg, opts);
            Contract.Assert(farg.Type != null);  // follows from postcondition of ResolveExpression
            Type s = SubstType(function.Formals[i].Type, e.TypeArgumentSubstitutions);
            if (!UnifyTypes(farg.Type, s)) {
              Error(e, "incorrect type of function argument {0} (expected {1}, got {2})", i, s, farg.Type);
            }
          }
          e.Type = SubstType(function.ResultType, e.TypeArgumentSubstitutions);
        }

        AddCallGraphEdge(opts.codeContext, function, e);
      }
    }

    private static void AddCallGraphEdge(ICodeContext callingContext, Function function, Expression e) {
      Contract.Requires(callingContext != null);
      Contract.Requires(function != null);
      Contract.Requires(e != null);
      // Resolution termination check
      ModuleDefinition callerModule = callingContext.EnclosingModule;
      ModuleDefinition calleeModule = function.EnclosingClass.Module;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        var caller = callingContext as ICallable;
        if (caller == null) {
          // don't add anything to the call graph after all
        } else if (caller is IteratorDecl) {
          callerModule.CallGraph.AddEdge(((IteratorDecl)callingContext).Member_MoveNext, function);
        } else {
          callerModule.CallGraph.AddEdge(caller, function);
          if (caller is Function) {
            FunctionCallExpr ee = e as FunctionCallExpr;
            if (ee != null) {
              ((Function)caller).AllCalls.Add(ee);
            }
          }
          if (caller == function) {
            function.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
          }
        }
      }
    }


    private ModuleSignature GetSignature(ModuleSignature sig) {
      if (useCompileSignatures) {
        while (sig.CompileSignature != null)
          sig = sig.CompileSignature;
      }
      return sig;
    }

    /// <summary>
    /// For a description, see DiscoverBoundsAux.
    /// </summary>
    public static List<ComprehensionExpr.BoundedPool> DiscoverBounds<VT>(IToken tok, List<VT> bvars, Expression expr, bool polarity, bool returnAllBounds, List<VT> missingBounds) where VT : IVariable {
      var pairs = DiscoverBoundsAux(tok, bvars, expr, polarity, returnAllBounds, false, missingBounds);
      if (pairs == null) {
        return null;
      }
      var bounds = new List<ComprehensionExpr.BoundedPool>();
      foreach (var pr in pairs) {
        Contract.Assert(1 <= pr.Item2.Count);
        bounds.AddRange(pr.Item2);
      }
      return bounds;
    }

    /// <summary>
    /// Tries to find a bounded pool for each of the bound variables "bvars" of "expr".  If this process
    /// fails, then "null" is returned and the bound variables for which the process fails are added to "missingBounds".
    /// If "returnAllBounds" is false, then:
    ///   -- at most one BoundedPool per variable is returned
    ///   -- every IntBoundedPool returned has both a lower and an upper bound
    ///   -- no SubSetBoundedPool or SuperSetBoundedPool is returned
    /// If "returnAllBounds" is true, then:
    ///   -- a variable may give rise to several BoundedPool's
    ///   -- IntBoundedPool bounds may have just one component
    ///   -- a non-null return value means that some bound were found for each variable (but, for example, perhaps one
    ///      variable only has lower bounds, no upper bounds)
    /// Requires "expr" to be successfully resolved.
    /// If "allowAnyIntegers", then integer variables will always be given a bound, but this bound may be WiggleWaggle if
    /// there is no better bound.
    /// </summary>
    public static List<Tuple<VT, List<ComprehensionExpr.BoundedPool>>> DiscoverBoundsAux<VT>(IToken tok, List<VT> bvars, Expression expr, bool polarity, bool returnAllBounds, bool allowAnyIntegers, List<VT> missingBounds) where VT : IVariable {
      Contract.Requires(tok != null);
      Contract.Requires(bvars != null);
      Contract.Requires(missingBounds != null);
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type != null);  // a sanity check (but not a complete proof) that "expr" has been resolved
      Contract.Ensures(
        (returnAllBounds && Contract.OldValue(missingBounds.Count) <= missingBounds.Count) ||
        (!returnAllBounds &&
         Contract.Result<List<Tuple<VT, List<ComprehensionExpr.BoundedPool>>>>() != null &&
         Contract.Result<List<Tuple<VT, List<ComprehensionExpr.BoundedPool>>>>().Count == bvars.Count &&
         Contract.OldValue(missingBounds.Count) == missingBounds.Count) ||
        (!returnAllBounds &&
         Contract.Result<List<Tuple<VT, List<ComprehensionExpr.BoundedPool>>>>() == null &&
         Contract.OldValue(missingBounds.Count) < missingBounds.Count));

      var allBounds = new List<Tuple<VT, List<ComprehensionExpr.BoundedPool>>>();
      bool foundError = false;
      foreach (var bv in bvars) {
        var c = TypeConstraint(bv, bv.Type);
        expr = polarity ? Expression.CreateAnd(c, expr) : Expression.CreateImplies(c, expr);
      }
      for (int j = 0; j < bvars.Count; j++) {
        var bv = bvars[j];
        var bounds = new List<ComprehensionExpr.BoundedPool>();
        if (bv.Type.IsBoolType) {
          // easy
          bounds.Add(new ComprehensionExpr.BoolBoundedPool());
        } else {
          bool foundBoundsForBv = false;
          if (bv.Type.IsIndDatatype && bv.Type.AsIndDatatype.HasFinitePossibleValues) {
            bounds.Add(new ComprehensionExpr.DatatypeBoundedPool(bv.Type.AsIndDatatype));
            foundBoundsForBv = true;
          }
          // Go through the conjuncts of the range expression to look for bounds.
          Expression lowerBound = null;
          Expression upperBound = null;
          if (returnAllBounds && lowerBound != null) {
            bounds.Add(new ComprehensionExpr.IntBoundedPool(lowerBound, upperBound));
            lowerBound = null;
            foundBoundsForBv = true;
          }
          foreach (var conjunct in NormalizedConjuncts(expr, polarity)) {
            var c = conjunct as BinaryExpr;
            if (c == null) {
              goto CHECK_NEXT_CONJUNCT;
            }
            var e0 = c.E0;
            var e1 = c.E1;
            int whereIsBv = SanitizeForBoundDiscovery(bvars, j, c.ResolvedOp, ref e0, ref e1);
            if (whereIsBv < 0) {
              goto CHECK_NEXT_CONJUNCT;
            }
            switch (c.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.InSet:
                if (whereIsBv == 0) {
                  bounds.Add(new ComprehensionExpr.SetBoundedPool(e1));
                  foundBoundsForBv = true;
                  if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
                }
                break;
              case BinaryExpr.ResolvedOpcode.Subset:
                if (returnAllBounds) {
                  if (whereIsBv == 0) {
                    bounds.Add(new ComprehensionExpr.SubSetBoundedPool(e1));
                  } else {
                    bounds.Add(new ComprehensionExpr.SuperSetBoundedPool(e0));
                  }
                  foundBoundsForBv = true;
                }
                break;
              case BinaryExpr.ResolvedOpcode.InMultiSet:
                if (whereIsBv == 0) {
                  bounds.Add(new ComprehensionExpr.SetBoundedPool(e1));
                  foundBoundsForBv = true;
                  if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
                }
                break;
              case BinaryExpr.ResolvedOpcode.InSeq:
                if (whereIsBv == 0) {
                  bounds.Add(new ComprehensionExpr.SeqBoundedPool(e1));
                  foundBoundsForBv = true;
                  if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
                }
                break;
              case BinaryExpr.ResolvedOpcode.InMap:
                if (whereIsBv == 0 && e1.Type.AsMapType.Finite) {
                  bounds.Add(new ComprehensionExpr.MapBoundedPool(e1));
                  foundBoundsForBv = true;
                  if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
                }
                break;
              case BinaryExpr.ResolvedOpcode.EqCommon:
                if (bv.Type is IntType) {
                  var otherOperand = whereIsBv == 0 ? e1 : e0;
                  bounds.Add(new ComprehensionExpr.IntBoundedPool(otherOperand, Expression.CreateIncrement(otherOperand, 1)));
                  foundBoundsForBv = true;
                  if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
                } else if (returnAllBounds && bv.Type is SetType) {
                  var otherOperand = whereIsBv == 0 ? e1 : e0;
                  bounds.Add(new ComprehensionExpr.SubSetBoundedPool(otherOperand));
                  foundBoundsForBv = true;
                }
                break;
              case BinaryExpr.ResolvedOpcode.Gt:
              case BinaryExpr.ResolvedOpcode.Ge:
                Contract.Assert(false); throw new cce.UnreachableException();  // promised by postconditions of NormalizedConjunct
              case BinaryExpr.ResolvedOpcode.Lt:
                if (e0.Type.IsNumericBased(Type.NumericPersuation.Int)) {
                  if (whereIsBv == 0 && upperBound == null) {
                    upperBound = e1;  // bv < E
                  } else if (whereIsBv == 1 && lowerBound == null) {
                    lowerBound = Expression.CreateIncrement(e0, 1);  // E < bv
                  }
                }
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                if (e0.Type.IsNumericBased(Type.NumericPersuation.Int)) {
                  if (whereIsBv == 0 && upperBound == null) {
                    upperBound = Expression.CreateIncrement(e1, 1);  // bv <= E
                  } else if (whereIsBv == 1 && lowerBound == null) {
                    lowerBound = e0;  // E <= bv
                  }
                }
                break;
              default:
                break;
            }
            if ((lowerBound != null && upperBound != null) ||
                (returnAllBounds && (lowerBound != null || upperBound != null))) {
              // we have found two halves (or, in the case of returnAllBounds, we have found some bound)
              bounds.Add(new ComprehensionExpr.IntBoundedPool(lowerBound, upperBound));
              lowerBound = null;
              upperBound = null;
              foundBoundsForBv = true;
              if (!returnAllBounds) goto CHECK_NEXT_BOUND_VARIABLE;
            }
          CHECK_NEXT_CONJUNCT: ;
          }
          if (!foundBoundsForBv) {
            // we have checked every conjunct in the range expression and still have not discovered good bounds
            if (allowAnyIntegers && bv.Type is IntType) {
              bounds.Add(new AssignSuchThatStmt.WiggleWaggleBound());
            } else {
              missingBounds.Add(bv);  // record failing bound variable
              foundError = true;
            }
          }
        }
      CHECK_NEXT_BOUND_VARIABLE: ;  // should goto here only if the bound for the current variable has been discovered (otherwise, return with null from this method)
      allBounds.Add(new Tuple<VT, List<ComprehensionExpr.BoundedPool>>(bv, bounds));
      }
      return foundError ? null : allBounds;
    }

    static Expression TypeConstraint(IVariable bv, Type ty) {
      Contract.Requires(bv != null);
      Contract.Requires(ty != null);
      ty = ty.NormalizeExpand();
      var dd = ty.AsNewtype;
      if (dd != null) {
        var c = TypeConstraint(bv, dd.BaseType);
        if (dd.Var != null) {
          c = Expression.CreateAnd(c, new Translator().Substitute(dd.Constraint, dd.Var, Expression.CreateIdentExpr(bv)));
        }
        return c;
      }
      if (ty is NatType) {
        return Expression.CreateAtMost(Expression.CreateIntLiteral(bv.Tok, 0), Expression.CreateIdentExpr(bv));
      }
      return Expression.CreateBoolLiteral(bv.Tok, true);
    }

    /// <summary>
    /// If the return value is negative, the resulting "e0" and "e1" should not be used.
    /// Otherwise, the following is true on return:
    /// The new "e0 op e1" is equivalent to the old "e0 op e1".
    /// One of "e0" and "e1" is the identifier "boundVars[bvi]"; the return value is either 0 or 1, and indicates which.
    /// The other of "e0" and "e1" is an expression whose free variables are not among "boundVars[bvi..]".
    /// Ensures that the resulting "e0" and "e1" are not ConcreteSyntaxExpression's.
    /// </summary>
    static int SanitizeForBoundDiscovery<VT>(List<VT> boundVars, int bvi, BinaryExpr.ResolvedOpcode op, ref Expression e0, ref Expression e1) where VT : IVariable {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(0 <= bvi && bvi < boundVars.Count);
      Contract.Ensures(Contract.Result<int>() < 2);
      Contract.Ensures(!(Contract.ValueAtReturn(out e0) is ConcreteSyntaxExpression));
      Contract.Ensures(!(Contract.ValueAtReturn(out e1) is ConcreteSyntaxExpression));

      IVariable bv = boundVars[bvi];
      e0 = e0.Resolved;
      e1 = e1.Resolved;

      // make an initial assessment of where bv is; to continue, we need bv to appear in exactly one operand
      var fv0 = FreeVariables(e0);
      var fv1 = FreeVariables(e1);
      Expression thisSide;
      Expression thatSide;
      int whereIsBv;
      if (fv0.Contains(bv)) {
        if (fv1.Contains(bv)) {
          return -1;
        }
        whereIsBv = 0;
        thisSide = e0; thatSide = e1;
      } else if (fv1.Contains(bv)) {
        whereIsBv = 1;
        thisSide = e1; thatSide = e0;
      } else {
        return -1;
      }

      // Next, clean up the side where bv is by adjusting both sides of the expression
      switch (op) {
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Lt:
          // Repeatedly move additive or subtractive terms from thisSide to thatSide
          while (true) {
            var bin = thisSide as BinaryExpr;
            if (bin == null) {
              break;  // done simplifying

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
              // Change "A+B op C" into either "A op C-B" or "B op C-A", depending on where we find bv among A and B.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, thatSide, bin.E1);
              } else {
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, thatSide, bin.E0);
              }
              ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
              thatSide.Type = bin.Type;

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
              // Change "A-B op C" in a similar way.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                // change to "A op C+B"
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Add, thatSide, bin.E1);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Add;
              } else {
                // In principle, change to "-B op C-A" and then to "B dualOp A-C".  But since we don't want
                // to change "op", we instead end with "A-C op B" and switch the mapping of thisSide/thatSide
                // to e0/e1 (by inverting "whereIsBv").
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, bin.E0, thatSide);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
                whereIsBv = 1 - whereIsBv;
              }
              thatSide.Type = bin.Type;

            } else {
              break;  // done simplifying
            }
          }
          break;

        default:
          break;
      }

      // Now, see if the interesting side is simply bv itself
      if (thisSide is IdentifierExpr && ((IdentifierExpr)thisSide).Var == bv) {
        // we're cool
      } else {
        // no, the situation is more complicated than we care to understand
        return -1;
      }

      // Finally, check that the other side does not contain "bv" or any of the bound variables
      // listed after "bv" in the quantifier.
      var fv = FreeVariables(thatSide);
      for (int i = bvi; i < boundVars.Count; i++) {
        if (fv.Contains(boundVars[i])) {
          return -1;
        }
      }

      // As we return, also return the adjusted sides
      if (whereIsBv == 0) {
        e0 = thisSide; e1 = thatSide;
      } else {
        e0 = thatSide; e1 = thisSide;
      }
      return whereIsBv;
    }

    /// <summary>
    /// Returns all conjuncts of "expr" in "polarity" positions.  That is, if "polarity" is "true", then
    /// returns the conjuncts of "expr" in positive positions; else, returns the conjuncts of "expr" in
    /// negative positions.  The method considers a canonical-like form of the expression that pushes
    /// negations inwards far enough that one can determine what the result is going to be (so, almost
    /// a negation normal form).
    /// As a convenience, arithmetic inequalities are rewritten so that the negation of an arithmetic
    /// inequality is never returned and the comparisons > and >= are never returned; the negation of
    /// a common equality or disequality is rewritten analogously.
    /// Requires "expr" to be successfully resolved.
    /// Ensures that what is returned is not a ConcreteSyntaxExpression.
    /// </summary>
    static IEnumerable<Expression> NormalizedConjuncts(Expression expr, bool polarity) {
      // We consider 5 cases.  To describe them, define P(e)=Conjuncts(e,true) and N(e)=Conjuncts(e,false).
      //   *  X ==> Y    is treated as a shorthand for !X || Y, and so is described by the remaining cases
      //   *  X && Y     P(_) = P(X),P(Y)    and    N(_) = !(X && Y)
      //   *  X || Y     P(_) = (X || Y)     and    N(_) = N(X),N(Y)
      //   *  !X         P(_) = N(X)         and    N(_) = P(X)
      //   *  else       P(_) = else         and    N(_) = !else
      // So for ==>, we have:
      //   *  X ==> Y    P(_) = P(!X || Y) = (!X || Y) = (X ==> Y)
      //                 N(_) = N(!X || Y) = N(!X),N(Y) = P(X),N(Y)
      expr = expr.Resolved;

      // Binary expressions
      var b = expr as BinaryExpr;
      if (b != null) {
        bool breakDownFurther = false;
        bool p0 = polarity;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            breakDownFurther = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            breakDownFurther = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Imp:
            breakDownFurther = !polarity;
            p0 = !p0;
            break;
          default:
            break;
        }
        if (breakDownFurther) {
          foreach (var c in NormalizedConjuncts(b.E0, p0)) {
            yield return c;
          }
          foreach (var c in NormalizedConjuncts(b.E1, polarity)) {
            yield return c;
          }
          yield break;
        }
      }

      // Unary expression
      var u = expr as UnaryOpExpr;
      if (u != null && u.Op == UnaryOpExpr.Opcode.Not) {
        foreach (var c in NormalizedConjuncts(u.E, !polarity)) {
          yield return c;
        }
        yield break;
      }

      // no other case applied, so return the expression or its negation, but first clean it up a little
      b = expr as BinaryExpr;
      if (b != null) {
        BinaryExpr.Opcode newOp;
        BinaryExpr.ResolvedOpcode newROp;
        bool swapOperands;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Gt:  // A > B         yield polarity ? (B < A) : (A <= B);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Ge:  // A >= B        yield polarity ? (B <= A) : (A < B);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Le:  // A <= B        yield polarity ? (A <= B) : (B < A);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Lt:  // A < B         yield polarity ? (A < B) : (B <= A);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:  // A == B         yield polarity ? (A == B) : (A != B);
            newOp = polarity ? BinaryExpr.Opcode.Eq : BinaryExpr.Opcode.Neq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.EqCommon : BinaryExpr.ResolvedOpcode.NeqCommon;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NeqCommon:  // A != B         yield polarity ? (A != B) : (A == B);
            newOp = polarity ? BinaryExpr.Opcode.Neq : BinaryExpr.Opcode.Eq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NeqCommon : BinaryExpr.ResolvedOpcode.EqCommon;
            swapOperands = false;
            break;
          default:
            goto JUST_RETURN_IT;
        }
        if (newROp != b.ResolvedOp || swapOperands) {
          b = new BinaryExpr(b.tok, newOp, swapOperands ? b.E1 : b.E0, swapOperands ? b.E0 : b.E1);
          b.ResolvedOp = newROp;
          b.Type = Type.Bool;
          yield return b;
          yield break;
        }
      }
    JUST_RETURN_IT: ;
      if (polarity) {
        yield return expr;
      } else {
        expr = new UnaryOpExpr(expr.tok, UnaryOpExpr.Opcode.Not, expr);
        expr.Type = Type.Bool;
        yield return expr;
      }
    }

    /// <summary>
    /// Returns the set of free variables in "expr".
    /// Requires "expr" to be successfully resolved.
    /// Ensures that the set returned has no aliases.
    /// </summary>
    static ISet<IVariable> FreeVariables(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new HashSet<IVariable>() { e.Var };

      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        var s = FreeVariables(e.LogicalBody());
        foreach (var bv in e.BoundVars) {
          s.Remove(bv);
        }
        return s;

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var s = FreeVariables(e.Source);
        foreach (MatchCaseExpr mc in e.Cases) {
          var t = FreeVariables(mc.Body);
          foreach (var bv in mc.Arguments) {
            t.Remove(bv);
          }
          s.UnionWith(t);
        }
        return s;

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        var s = FreeVariables(e.Term);
        if (e.Range != null) {
          s.UnionWith(FreeVariables(e.Range));
        }
        foreach (var fe in e.Reads) {
          s.UnionWith(FreeVariables(fe.E));
        }
        foreach (var bv in e.BoundVars) {
          s.Remove(bv);
        }
        return s;

      } else {
        ISet<IVariable> s = null;
        foreach (var e in expr.SubExpressions) {
          var t = FreeVariables(e);
          if (s == null) {
            s = t;
          } else {
            s.UnionWith(t);
          }
        }
        return s == null ? new HashSet<IVariable>() : s;
      }
    }

    void ResolveReceiver(Expression expr, ResolveOpts opts) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is ThisExpr && !expr.WasResolved()) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        Contract.Assume(currentClass != null);  // this is really a precondition, in this case
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, opts);
      }
    }

    void ResolveSeqSelectExpr(SeqSelectExpr e, ResolveOpts opts, bool allowNonUnitArraySelection) {
      Contract.Requires(e != null);
      if (e.Type != null) {
        // already resolved
        return;
      }

      bool seqErr = false;
      ResolveExpression(e.Seq, opts);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
      Type elementType = new InferredTypeProxy();
      Type domainType = new InferredTypeProxy();
      Type argType = new InferredTypeProxy();

      IndexableTypeProxy expectedType = new IndexableTypeProxy(domainType, elementType, argType, true, true, true);
      if (!UnifyTypes(e.Seq.Type, expectedType)) {
        Error(e, "sequence/array/multiset/map selection requires a sequence, array, multiset, or map (got {0})", e.Seq.Type);
        seqErr = true;
      }
      if (!e.SelectOne)  // require sequence or array
      {
        if (!allowNonUnitArraySelection) {
          // require seq
          if (!UnifyTypes(expectedType, new SeqType(new InferredTypeProxy()))) {
            Error(e, "selection requires a sequence (got {0})", e.Seq.Type);
          }
        } else {
          if (UnifyTypes(expectedType, new MapType(true, new InferredTypeProxy(), new InferredTypeProxy()))) {
            Error(e, "cannot multiselect a map (got {0} as map type)", e.Seq.Type);
          } else if (UnifyTypes(expectedType, new MapType(false, new InferredTypeProxy(), new InferredTypeProxy()))) {
            Error(e, "cannot multiselect an imap (got {0} as imap type)", e.Seq.Type);
          }
        }
      }
      if (e.E0 != null) {
        ResolveExpression(e.E0, opts);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E0.Type, domainType)) {
          Error(e.E0, "sequence/array/multiset/map selection requires {1} indices (got {0})", e.E0.Type, domainType);
        }
      }
      if (e.E1 != null) {
        ResolveExpression(e.E1, opts);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        var domType = e.E0 == null ? domainType : new OperationTypeProxy(true, false, false, false, false);  // reuse 'domainType' if .E0 did not use it; otherwise, create a new proxy to allow .E1 to be any integer-based numeric type, independent of the integer-based numeric type used by .E0
        if (!UnifyTypes(e.E1.Type, domType)) {
          Error(e.E1, "sequence/array/multiset/map selection requires {1} indices (got {0})", e.E1.Type, domType);
        }
      }
      if (!seqErr) {
        if (e.SelectOne) {
          e.Type = elementType;
        } else {
          e.Type = new SeqType(elementType);
        }
      }
    }

    /// <summary>
    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// </summary>
    public static BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, Type operandType) {
      Contract.Requires(operandType != null);
      operandType = operandType.NormalizeExpand();
      switch (op) {
        case BinaryExpr.Opcode.Iff: return BinaryExpr.ResolvedOpcode.Iff;
        case BinaryExpr.Opcode.Imp: return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.Exp: return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.And: return BinaryExpr.ResolvedOpcode.And;
        case BinaryExpr.Opcode.Or: return BinaryExpr.ResolvedOpcode.Or;
        case BinaryExpr.Opcode.Eq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetEq;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetEq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqEq;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapEq;
          } else {
            return BinaryExpr.ResolvedOpcode.EqCommon;
          }
        case BinaryExpr.Opcode.Neq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetNeq;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetNeq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqNeq;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapNeq;
          } else {
            return BinaryExpr.ResolvedOpcode.NeqCommon;
          }
        case BinaryExpr.Opcode.Disjoint:
          if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetDisjoint;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapDisjoint;
          } else {
            return BinaryExpr.ResolvedOpcode.Disjoint;
          }
        case BinaryExpr.Opcode.Lt:
          if (operandType.IsIndDatatype || (operandType is DatatypeProxy && !((DatatypeProxy)operandType).Co)) {
            return BinaryExpr.ResolvedOpcode.RankLt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSubset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.ProperMultiSubset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.ProperPrefix;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.LtChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Lt;
          }
        case BinaryExpr.Opcode.Le:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Subset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSubset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Prefix;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.LeChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Le;
          }
        case BinaryExpr.Opcode.Add:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Union;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetUnion;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapUnion;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Concat;
          } else {
            return BinaryExpr.ResolvedOpcode.Add;
          }
        case BinaryExpr.Opcode.Sub:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetDifference;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetDifference;
          } else {
            return BinaryExpr.ResolvedOpcode.Sub;
          }
        case BinaryExpr.Opcode.Mul:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Intersection;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetIntersection;
          } else {
            return BinaryExpr.ResolvedOpcode.Mul;
          }
        case BinaryExpr.Opcode.Gt:
          if (operandType.IsDatatype) {
            return BinaryExpr.ResolvedOpcode.RankGt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSuperset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.ProperMultiSuperset;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.GtChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Gt;
          }
        case BinaryExpr.Opcode.Ge:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Superset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSuperset;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.GeChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Ge;
          }
        case BinaryExpr.Opcode.In:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.InSet;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.InMultiSet;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.InMap;
          } else {
            return BinaryExpr.ResolvedOpcode.InSeq;
          }
        case BinaryExpr.Opcode.NotIn:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.NotInSet;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.NotInMultiSet;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.NotInMap;
          } else {
            return BinaryExpr.ResolvedOpcode.NotInSeq;
          }
        case BinaryExpr.Opcode.Div: return BinaryExpr.ResolvedOpcode.Div;
        case BinaryExpr.Opcode.Mod: return BinaryExpr.ResolvedOpcode.Mod;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
      }
    }

    /// <summary>
    /// Returns whether or not 'expr' has any subexpression that uses some feature (like a ghost or quantifier)
    /// that is allowed only in specification contexts.
    /// Requires 'expr' to be a successfully resolved expression.
    /// </summary>
    bool UsesSpecFeatures(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

      if (expr is LiteralExpr) {
        return false;
      } else if (expr is ThisExpr) {
        return false;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return cce.NonNull(e.Var).IsGhost;
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        return dtv.Arguments.Exists(arg => UsesSpecFeatures(arg));
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return e.Elements.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        return e.Elements.Exists(p => UsesSpecFeatures(p.A) || UsesSpecFeatures(p.B));
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr) expr;
        if (e.Member != null) {
          return cce.NonNull(e.Member).IsGhost || UsesSpecFeatures(e.Obj);
        } else {
          return false;
        }
    } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               (e.E0 != null && UsesSpecFeatures(e.E0)) ||
               (e.E1 != null && UsesSpecFeatures(e.E1));
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        return UsesSpecFeatures(e.Array) || e.Indices.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               UsesSpecFeatures(e.Index) ||
               UsesSpecFeatures(e.Value);
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        if (cce.NonNull(e.Function).IsGhost) {
          return true;
        }
        return e.Args.Exists(arg => UsesSpecFeatures(arg));
      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        return UsesSpecFeatures(e.Function) || e.Args.Exists(UsesSpecFeatures);
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        var unaryOpExpr = e as UnaryOpExpr;
        if (unaryOpExpr != null && unaryOpExpr.Op == UnaryOpExpr.Opcode.Fresh) {
          return true;
        }
        return UsesSpecFeatures(e.E);
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        switch (e.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            return true;
          default:
            return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1);
        }
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            return true;
          default:
            break;
        }
        return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1) || UsesSpecFeatures(e.E2);
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          return Contract.Exists(e.RHSs, ee => UsesSpecFeatures(ee)) || UsesSpecFeatures(e.Body);
        } else {
          return true;  // let-such-that is always ghost
        }
      } else if (expr is NamedExpr) {
        return moduleInfo.IsGhost ? false : UsesSpecFeatures(((NamedExpr)expr).Body);
      } else if (expr is ComprehensionExpr) {
        if (expr is QuantifierExpr && ((QuantifierExpr)expr).Bounds == null) {
          return true;  // the quantifier cannot be compiled if the resolver found no bounds
        }
        return Contract.Exists(expr.SubExpressions, se => UsesSpecFeatures(se));
      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        return (e.Range != null && UsesSpecFeatures(e.Range)) || (e.Term != null && UsesSpecFeatures(e.Term));
      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        return (UsesSpecFeatures(e.Range)) || (UsesSpecFeatures(e.Term));
      } else if (expr is LambdaExpr) {
        return Contract.Exists(expr.SubExpressions, UsesSpecFeatures);
      } else if (expr is WildcardExpr) {
        return false;
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        return UsesSpecFeatures(e.Test) || UsesSpecFeatures(e.Thn) || UsesSpecFeatures(e.Els);
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        if (UsesSpecFeatures(me.Source)) {
          return true;
        }
        return me.Cases.Exists(mc => UsesSpecFeatures(mc.Body));
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return e.ResolvedExpression != null && UsesSpecFeatures(e.ResolvedExpression);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
}


    /// <summary>
    /// This method adds to "coConclusions" all copredicate calls and codatatype equalities that occur
    /// in positive positions and not under existential quantification.  If "expr" is the postcondition
    /// of a colemma, then the "coConclusions" are the subexpressions that need to be replaced in order
    /// to create the postcondition of the corresponding prefix lemma.
    /// </summary>
    void CheckCoLemmaConclusions(Expression expr, bool position, ISet<Expression> coConclusions) {
      Contract.Requires(expr != null);
      if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        CheckCoLemmaConclusions(e.ResolvedExpression, position, coConclusions);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        // For simplicity, only look in the body of the let expression, that is, ignoring the RHS of the
        // binding and ignoring what that binding would expand to in the body.
        CheckCoLemmaConclusions(e.Body, position, coConclusions);

      } else if (expr is UnaryExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Not) {
          CheckCoLemmaConclusions(e.E, !position, coConclusions);
        }

      } else if (expr is BinaryExpr) {
        var bin = (BinaryExpr)expr;
        if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And || bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          CheckCoLemmaConclusions(bin.E0, position, coConclusions);
          CheckCoLemmaConclusions(bin.E1, position, coConclusions);
        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
          CheckCoLemmaConclusions(bin.E0, !position, coConclusions);
          CheckCoLemmaConclusions(bin.E1, position, coConclusions);
        } else if (position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon && bin.E0.Type.IsCoDatatype) {
          coConclusions.Add(bin);
        } else if (!position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon && bin.E0.Type.IsCoDatatype) {
          coConclusions.Add(bin);
        }

      } else if (expr is ITEExpr) {
        var ite = (ITEExpr)expr;
        CheckCoLemmaConclusions(ite.Thn, position, coConclusions);
        CheckCoLemmaConclusions(ite.Els, position, coConclusions);

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        CheckCoLemmaConclusions(e.E, position, coConclusions);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        CheckCoLemmaConclusions(e.E, position, coConclusions);

      } else if (expr is FunctionCallExpr && position) {
        var fexp = (FunctionCallExpr)expr;
        if (fexp.Function is CoPredicate) {
          coConclusions.Add(fexp);
        }
      }
    }
  }

  class CoCallResolution
  {
    readonly Function currentFunction;
    readonly bool dealsWithCodatatypes;
    public bool HasIntraClusterCallsInDestructiveContexts = false;
    public readonly List<CoCallInfo> FinalCandidates = new List<CoCallInfo>();

    public CoCallResolution(Function currentFunction, bool dealsWithCodatatypes) {
      Contract.Requires(currentFunction != null);
      this.currentFunction = currentFunction;
      this.dealsWithCodatatypes = dealsWithCodatatypes;
    }

    /// <summary>
    /// Determines which calls in "expr" can be considered to be co-calls, which co-constructor
    /// invocations host such co-calls, and which destructor operations are not allowed.
    /// Also records whether or not there are any intra-cluster calls in a destructive context.
    /// Assumes "expr" to have been successfully resolved.
    /// </summary>
    public void CheckCoCalls(Expression expr) {
      Contract.Requires(expr != null);
      CheckCoCalls(expr, 0, null, FinalCandidates);
    }

    public struct CoCallInfo
    {
      public readonly FunctionCallExpr CandidateCall;
      public readonly DatatypeValue EnclosingCoConstructor;
      public CoCallInfo(FunctionCallExpr candidateCall, DatatypeValue enclosingCoConstructor) {
        Contract.Requires(candidateCall != null);
        Contract.Requires(enclosingCoConstructor != null);
        CandidateCall = candidateCall;
        EnclosingCoConstructor = enclosingCoConstructor;
      }
    }

    /// <summary>
    /// Recursively goes through the entire "expr".  Every call within the same recursive cluster is a potential
    /// co-call.  If the call is determined not to be a co-recursive call, then its .CoCall field is filled in;
    /// if the situation deals with co-datatypes, then one of the NoBecause... values is chosen (rather
    /// than just No), so that any error message that may later be produced when trying to prove termination of the
    /// recursive call can include a note pointing out that the call was not selected to be a co-call.
    /// If the call looks like it is guarded, then it is added to the list "coCandicates", so that a later analysis
    /// can either set all of those .CoCall fields to Yes or to NoBecauseRecursiveCallsInDestructiveContext, depending
    /// on other intra-cluster calls.
    /// The "destructionLevel" indicates how many pending co-destructors the context has.  It may be infinity (int.MaxValue)
    /// if the enclosing context has no easy way of controlling the uses of "expr" (for example, if the enclosing context
    /// passes "expr" to a function or binds "expr" to a variable).  It is never negative -- excess co-constructors are
    /// not considered an asset, and any immediately enclosing co-constructor is passed in as a non-null "coContext" anyway.
    /// "coContext" is non-null if the immediate context is a co-constructor.
    /// </summary>
    void CheckCoCalls(Expression expr, int destructionLevel, DatatypeValue coContext, List<CoCallInfo> coCandidates) {
      Contract.Requires(expr != null);
      Contract.Requires(0 <= destructionLevel);
      Contract.Requires(coCandidates != null);

      expr = expr.Resolved;
      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        if (e.Ctor.EnclosingDatatype is CoDatatypeDecl) {
          int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel == 0 ? 0 : destructionLevel - 1;
          foreach (var arg in e.Arguments) {
            CheckCoCalls(arg, dl, e, coCandidates);
          }
          return;
        }
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member.EnclosingClass is CoDatatypeDecl) {
          int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel + 1;
          CheckCoCalls(e.Obj, dl, null, coCandidates);
          return;
        }
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) {
          // Equality and disequality (for any type that may contain a co-datatype) are as destructive as can be--in essence,
          // they destruct the values indefinitely--so don't allow any co-recursive calls in the operands.
          CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
          return;
        }
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        if (e.Op == TernaryExpr.Opcode.PrefixEqOp || e.Op == TernaryExpr.Opcode.PrefixNeqOp) {
          // Prefix equality and disequality (for any type that may contain a co-datatype) are destructive.
          CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E2, int.MaxValue, null, coCandidates);
          return;
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        CheckCoCalls(e.Source, int.MaxValue, null, coCandidates);
        foreach (var kase in e.Cases) {
          CheckCoCalls(kase.Body, destructionLevel, null, coCandidates);
        }
        return;
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        // First, consider the arguments of the call, making sure that they do not include calls within the recursive cluster.
        // (Note, if functions could have a "destruction level" declaration that promised to only destruct its arguments by
        // so much, then some recursive calls within the cluster could be allowed.)
        foreach (var arg in e.Args) {
          CheckCoCalls(arg, int.MaxValue, null, coCandidates);
        }
        // Second, investigate the possibility that this call itself may be a candidate co-call
        if (e.Name != "requires" && ModuleDefinition.InSameSCC(currentFunction, e.Function)) {
          // This call goes to another function in the same recursive cluster
          if (destructionLevel > 0) {
            // a potentially destructive context
            HasIntraClusterCallsInDestructiveContexts = true;  // this says we found an intra-cluster call unsuitable for recursion, if there were any co-recursive calls
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext;
            }
          } else if (coContext == null) {
            // no immediately enclosing co-constructor
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded;
            }
          } else if (e.Function.Reads.Count != 0) {
            // this call is disqualified from being a co-call, because of side effects
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects;
            }
          } else if (e.Function.Ens.Count != 0) {
            // this call is disqualified from being a co-call, because it has a postcondition
            // (a postcondition could be allowed, as long as it does not get to be used with
            // co-recursive calls, because that could be unsound; for example, consider
            // "ensures false;")
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasPostcondition;
            }
          } else {
            // e.CoCall is not filled in here, but will be filled in when the list of candidates are processed
            coCandidates.Add(new CoCallInfo(e, coContext));
          }
        }
        return;
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // here, "coContext" is passed along (the use of "old" says this must be ghost code, so the compiler does not need to handle this case)
        CheckCoCalls(e.E, destructionLevel, coContext, coCandidates);
        return;
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var rhs in e.RHSs) {
          CheckCoCalls(rhs, int.MaxValue, null, coCandidates);
        }
        CheckCoCalls(e.Body, destructionLevel, null, coCandidates);
        return;
      }

      // Default handling:
      foreach (var ee in expr.SubExpressions) {
        CheckCoCalls(ee, destructionLevel, null, coCandidates);
      }
    }
  }

  class Scope<Thing> where Thing : class
  {
    [Rep]
    readonly List<string> names = new List<string>();  // a null means a marker
    [Rep]
    readonly List<Thing> things = new List<Thing>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(names != null);
      Contract.Invariant(things != null);
      Contract.Invariant(names.Count == things.Count);
      Contract.Invariant(-1 <= scopeSizeWhereInstancesWereDisallowed && scopeSizeWhereInstancesWereDisallowed <= names.Count);
    }

    int scopeSizeWhereInstancesWereDisallowed = -1;

    public bool AllowInstance {
      get { return scopeSizeWhereInstancesWereDisallowed == -1; }
      set {
        Contract.Requires(AllowInstance && !value);  // only allowed to change from true to false (that's all that's currently needed in Dafny); Pop is what can make the change in the other direction
        scopeSizeWhereInstancesWereDisallowed = names.Count;
      }
    }

    public void PushMarker() {
      names.Add(null);
      things.Add(null);
    }

    public void PopMarker() {
      int n = names.Count;
      while (true) {
        n--;
        if (names[n] == null) {
          break;
        }
      }
      names.RemoveRange(n, names.Count - n);
      things.RemoveRange(n, things.Count - n);
      if (names.Count < scopeSizeWhereInstancesWereDisallowed) {
        scopeSizeWhereInstancesWereDisallowed = -1;
      }
    }

    // Pushes name-->thing association and returns "true", if name has not already been pushed since the last marker.
    // If name already has been pushed since the last marker, does nothing and returns "false".
    public bool Push(string name, Thing thing) {
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      if (Find(name, true) != null) {
        return false;
      } else {
        names.Add(name);
        things.Add(thing);
        return true;
      }
    }

    Thing Find(string name, bool topScopeOnly) {
      Contract.Requires(name != null);
      for (int n = names.Count; 0 <= --n; ) {
        if (names[n] == null) {
          if (topScopeOnly) {
            return null;  // not present
          }
        } else if (names[n] == name) {
          Thing t = things[n];
          Contract.Assert(t != null);
          return t;
        }
      }
      return null;  // not present
    }

    public Thing Find(string name) {
      Contract.Requires(name != null);
      return Find(name, false);
    }

    public bool ContainsDecl(Thing t) {
      return things.Exists(thing => thing == t);
    }
  }
}
