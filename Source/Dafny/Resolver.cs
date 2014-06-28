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

    class AmbiguousTopLevelDecl : TopLevelDecl  // only used with "classes"
    {
      readonly TopLevelDecl A;
      readonly TopLevelDecl B;
      public AmbiguousTopLevelDecl(ModuleDefinition m, TopLevelDecl a, TopLevelDecl b)
        : base(a.tok, a.Name + "/" + b.Name, m, new List<TypeParameter>(), null) {
        A = a;
        B = b;
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

    class AmbiguousMemberDecl : MemberDecl  // only used with "classes"
    {
      readonly MemberDecl A;
      readonly MemberDecl B;
      public AmbiguousMemberDecl(ModuleDefinition m, MemberDecl a, MemberDecl b)
        : base(a.tok, a.Name + "/" + b.Name, a.IsStatic, a.IsGhost, null) {
        A = a;
        B = b;
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
    //Dictionary<string/*!*/, Tuple<DatatypeCtor, bool>> allDatatypeCtors;

    readonly Dictionary<ClassDecl/*!*/, Dictionary<string/*!*/, MemberDecl/*!*/>/*!*/>/*!*/ classMembers = new Dictionary<ClassDecl/*!*/, Dictionary<string/*!*/, MemberDecl/*!*/>/*!*/>();
    readonly Dictionary<DatatypeDecl/*!*/, Dictionary<string/*!*/, MemberDecl/*!*/>/*!*/>/*!*/ datatypeMembers = new Dictionary<DatatypeDecl/*!*/, Dictionary<string/*!*/, MemberDecl/*!*/>/*!*/>();
    readonly Dictionary<DatatypeDecl/*!*/, Dictionary<string/*!*/, DatatypeCtor/*!*/>/*!*/>/*!*/ datatypeCtors = new Dictionary<DatatypeDecl/*!*/, Dictionary<string/*!*/, DatatypeCtor/*!*/>/*!*/>();
    readonly Graph<ModuleDecl/*!*/>/*!*/ dependencies = new Graph<ModuleDecl/*!*/>();
    private ModuleSignature systemNameInfo = null;
    private bool useCompileSignatures = false;

    public Resolver(Program prog) {
      Contract.Requires(prog != null);
      builtIns = prog.BuiltIns;
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
      var opaqueRewriter = new OpaqueFunctionRewriter();
      rewriters.Add(new AutoReqFunctionRewriter(this, opaqueRewriter));
      rewriters.Add(opaqueRewriter);

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

    public static Expression FrameToObjectSet(List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      List<Expression> sets = new List<Expression>();
      List<Expression> singletons = null;
      int tmpVarCount = 0;
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        if (fe.E is WildcardExpr) {
          // drop wildcards altogether
        } else {
          Expression e = fe.E;  // keep only fe.E, drop any fe.Field designation
          Contract.Assert(e.Type != null);  // should have been resolved already
          if (e.Type.IsRefType) {
            // e represents a singleton set
            if (singletons == null) {
              singletons = new List<Expression>();
            }
            singletons.Add(e);
          } else if (e.Type is SeqType) {
            // e represents a sequence
            // Add:  set x :: x in e
            var bv = new BoundVar(e.tok, "_s2s_" + tmpVarCount, ((SeqType)e.Type).Arg);
            tmpVarCount++;
            var bvIE = new IdentifierExpr(e.tok, bv.Name);
            bvIE.Var = bv;  // resolve here
            bvIE.Type = bv.Type;  // resolve here
            var sInE = new BinaryExpr(e.tok, BinaryExpr.Opcode.In, bvIE, e);
            sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InSeq;  // resolve here
            sInE.Type = Type.Bool;  // resolve here
            var s = new SetComprehension(e.tok, new List<BoundVar>() { bv }, sInE, bvIE);
            s.Type = new SetType(new ObjectType());  // resolve here
            sets.Add(s);
          } else {
            // e is already a set
            Contract.Assert(e.Type is SetType);
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
        } else if (d is ArbitraryTypeDecl) {
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
          var valid = new Predicate(iter.tok, "Valid", false, true, new List<TypeParameter>(), iter.tok,
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
                  // create prefix predicate
                  cop.PrefixPredicate = new PrefixPredicate(cop.tok, extraName, cop.IsStatic,
                    cop.TypeArgs.ConvertAll(cloner.CloneTypeParam), cop.OpenParen, k, formals,
                    cop.Req.ConvertAll(cloner.CloneExpr), cop.Reads.ConvertAll(cloner.CloneFrameExpr), cop.Ens.ConvertAll(cloner.CloneExpr),
                    new Specification<Expression>(new List<Expression>() { new IdentifierExpr(cop.tok, k.Name) }, null),
                    cop.Body, null, cop);
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
                  com.PrefixLemma = new PrefixLemma(com.tok, extraName, com.IsStatic,
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
              Error(m, "More than one default constructor");
            } else {
              Error(m, "Duplicate member name: {0}", m.Name);
            }
            if (m is Constructor) {
              hasConstructor = true;
            }
          }
          cl.HasConstructor = hasConstructor;
          if (cl.IsDefaultClass) {
            foreach (MemberDecl m in cl.Members) {
              if (m.IsStatic && (m is Function || m is Method)) {
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

      if (d is ArbitraryTypeDecl) {
        var dd = (ArbitraryTypeDecl)d;
        return new ArbitraryTypeDecl(dd.tok, dd.Name, m, dd.EqualitySupport, null);
      } else if (d is TupleTypeDecl) {
        var dd = (TupleTypeDecl)d;
        return new TupleTypeDecl(dd.Dims, dd.Module);
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(dd.tok, dd.Name, m, tps, ctors, null);
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(dd.tok, dd.Name, m, tps, ctors, null);
        return dt;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        if (dd is DefaultClassDecl) {
          return new DefaultClassDecl(m, mm);
        } else return new ClassDecl(dd.tok, dd.Name, m, tps, mm, null);
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl) {
          return new LiteralModuleDecl(((LiteralModuleDecl)d).ModuleDef, m);
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          var alias = new AliasModuleDecl(a.Path, a.tok, m, a.Opened);
          alias.ModuleReference = a.ModuleReference;
          alias.Signature = a.Signature;
          return alias;
        } else if (d is ModuleFacadeDecl) {
          var abs = (ModuleFacadeDecl)d;
          var sig = MakeAbstractSignature(abs.OriginalSignature, Name + "." + abs.Name, abs.Height, mods);
          var a = new ModuleFacadeDecl(abs.Path, abs.tok, m, abs.CompilePath, abs.Opened);
          a.Signature = sig;
          a.OriginalSignature = abs.OriginalSignature;
          return a;
        } else {
          Contract.Assert(false);  // unexpected declaration
          return null;  // to please compiler
        }
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }
    MemberDecl CloneMember(MemberDecl member) {
      if (member is Field) {
        Contract.Assert(!(member is SpecialField));  // we don't expect a SpecialField to be cloned (or do we?)
        var f = (Field)member;
        return new Field(f.tok, f.Name, f.IsGhost, f.IsMutable, f.IsUserMutable, CloneType(f.Type), null);
      } else if (member is Function) {
        var f = (Function)member;
        return CloneFunction(f.tok, f, f.IsGhost);
      } else {
        var m = (Method)member;
        return CloneMethod(m);
      }
    }
    TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(tp.tok, tp.Name);
    }

    DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(ct.tok, ct.Name, ct.Formals.ConvertAll(CloneFormal), null);
    }
    Formal CloneFormal(Formal formal) {
      return new Formal(formal.tok, formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost);
    }
    Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(CloneType(tt.Arg));
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(CloneType(tt.Arg));
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(CloneType(tt.Arg));
      } else if (t is MapType) {
        var tt = (MapType)t;
        return new MapType(CloneType(tt.Domain), CloneType(tt.Range));
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        return new UserDefinedType(tt.tok, tt.Name, tt.TypeArgs.ConvertAll(CloneType), tt.Path.ConvertAll(x => x));
      } else if (t is InferredTypeProxy) {
        return new InferredTypeProxy();
      } else if (t is ParamTypeProxy) {
        var tt = (ParamTypeProxy)t;
        return new ParamTypeProxy(CloneTypeParam(tt.orig));
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }
    Function CloneFunction(IToken tok, Function f, bool isGhost) {

      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);

      var ens = f.Ens.ConvertAll(CloneExpr);

      Expression body = CloneExpr(f.Body);

      if (f is Predicate) {
        return new Predicate(tok, f.Name, f.IsStatic, isGhost, tps, f.OpenParen, formals,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited, null, null);
      } else if (f is CoPredicate) {
        return new CoPredicate(tok, f.Name, f.IsStatic, tps, f.OpenParen, formals,
          req, reads, ens, body, null, null);
      } else {
        return new Function(tok, f.Name, f.IsStatic, isGhost, tps, f.OpenParen, formals, CloneType(f.ResultType),
          req, reads, ens, decreases, body, null, null);
      }
    }
    Method CloneMethod(Method m) {
      Contract.Requires(m != null);

      var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(CloneFormal);
      var req = m.Req.ConvertAll(CloneMayBeFreeExpr);
      var mod = CloneSpecFrameExpr(m.Mod);
      var decreases = CloneSpecExpr(m.Decreases);

      var ens = m.Ens.ConvertAll(CloneMayBeFreeExpr);

      if (m is Constructor) {
        return new Constructor(m.tok, m.Name, tps, ins,
          req, mod, ens, decreases, null, null, null);
      } else if (m is CoLemma) {
        return new CoLemma(m.tok, m.Name, m.IsStatic, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, null, null, null);
      } else if (m is Lemma) {
        return new Lemma(m.tok, m.Name, m.IsStatic, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, null, null, null);
      } else {
        return new Method(m.tok, m.Name, m.IsStatic, m.IsGhost, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, null, null, null);
      }
    }
    Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(CloneExpr);
      return new Specification<Expression>(ee, null);
    }
    Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(CloneFrameExpr);
      return new Specification<FrameExpression>(ee, null);
    }
    FrameExpression CloneFrameExpr(FrameExpression frame) {
      return new FrameExpression(frame.tok, CloneExpr(frame.E), frame.FieldName);
    }
    MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      return new MaybeFreeExpression(CloneExpr(expr.E), expr.IsFree);
    }
    BoundVar CloneBoundVar(BoundVar bv) {
      return new BoundVar(bv.tok, bv.Name, CloneType(bv.Type));
    }
    // ToDo: Remove this and use cloner
    Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e is StaticReceiverExpr) {
          return new StaticReceiverExpr(e.tok, CloneType(e.Type));
        } else if (e.Value == null) {
          return new LiteralExpr(e.tok);
        } else if (e.Value is bool) {
          return new LiteralExpr(e.tok, (bool)e.Value);
        } else if (e.Value is Basetypes.BigDec) {
          return new LiteralExpr(e.tok, (Basetypes.BigDec)e.Value);
        } else {
          return new LiteralExpr(e.tok, (BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        if (expr is ImplicitThisExpr) {
          return new ImplicitThisExpr(expr.tok);
        } else {
          return new ThisExpr(expr.tok);
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new IdentifierExpr(e.tok, e.Name);

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        return new DatatypeValue(e.tok, e.DatatypeName, e.MemberName, e.Arguments.ConvertAll(CloneExpr));

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (expr is SetDisplayExpr) {
          return new SetDisplayExpr(e.tok, e.Elements.ConvertAll(CloneExpr));
        } else if (expr is MultiSetDisplayExpr) {
          return new MultiSetDisplayExpr(e.tok, e.Elements.ConvertAll(CloneExpr));
        } else {
          Contract.Assert(expr is SeqDisplayExpr);
          return new SeqDisplayExpr(e.tok, e.Elements.ConvertAll(CloneExpr));
        }

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        List<ExpressionPair> pp = new List<ExpressionPair>();
        foreach (ExpressionPair p in e.Elements) {
          pp.Add(new ExpressionPair(CloneExpr(p.A), CloneExpr(p.B)));
        }
        return new MapDisplayExpr(expr.tok, pp);
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        return new ExprDotName(e.tok, CloneExpr(e.Obj), e.SuffixName);

      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        return new FieldSelectExpr(e.tok, CloneExpr(e.Obj), e.FieldName);

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return new SeqSelectExpr(e.tok, e.SelectOne, CloneExpr(e.Seq), CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        return new MultiSelectExpr(e.tok, CloneExpr(e.Array), e.Indices.ConvertAll(CloneExpr));

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return new SeqUpdateExpr(e.tok, CloneExpr(e.Seq), CloneExpr(e.Index), CloneExpr(e.Value));

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        return new FunctionCallExpr(e.tok, e.Name, CloneExpr(e.Receiver), e.OpenParen == null ? null : (e.OpenParen), e.Args.ConvertAll(CloneExpr));

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return new OldExpr(e.tok, CloneExpr(e.E));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(e.tok, CloneExpr(e.E));

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        return new FreshExpr(e.tok, CloneExpr(e.E));

      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        return new UnaryExpr(e.tok, e.Op, CloneExpr(e.E));

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return new BinaryExpr(e.tok, e.Op, CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return new TernaryExpr(e.tok, e.Op, CloneExpr(e.E0), CloneExpr(e.E1), CloneExpr(e.E2));

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        return CloneExpr(e.E);  // just clone the desugaring, since it's already available

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new LetExpr(e.tok, e.LHSs.ConvertAll(CloneCasePattern), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body), e.Exact);

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var tk = e.tok;
        var bvs = e.BoundVars.ConvertAll(CloneBoundVar);
        var range = CloneExpr(e.Range);
        var term = CloneExpr(e.Term);
        if (e is ForallExpr) {
          return new ForallExpr(tk, bvs, range, term, null);
        } else if (e is ExistsExpr) {
          return new ExistsExpr(tk, bvs, range, term, null);
        } else if (e is MapComprehension) {
          return new MapComprehension(tk, bvs, range, term);
        } else {
          Contract.Assert(e is SetComprehension);
          return new SetComprehension(tk, bvs, range, term);
        }

      } else if (expr is WildcardExpr) {
        return new WildcardExpr(expr.tok);

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return new StmtExpr(e.tok, (new Cloner()).CloneStmt(e.S), CloneExpr(e.E));

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(e.tok, CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is AutoGeneratedExpression) {
        var e = (AutoGeneratedExpression)expr;
        var a = CloneExpr(e.E);
        return new AutoGeneratedExpression(e.tok, a);

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E);  // skip the parentheses in the clone

      } else if (expr is IdentifierSequence) {
        var e = (IdentifierSequence)expr;
        var aa = e.Arguments == null ? null : e.Arguments.ConvertAll(CloneExpr);
        return new IdentifierSequence(e.Tokens.ConvertAll(tk => (tk)), e.OpenParen == null ? null : (e.OpenParen), aa);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(e.tok, CloneExpr(e.Source),
          e.Cases.ConvertAll(c => new MatchCaseExpr(c.tok, c.Id, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body))), e.UsesOptionalBraces);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        return new NegationExpression(e.tok, CloneExpr(e.E));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public CasePattern CloneCasePattern(CasePattern pat) {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        return new CasePattern(pat.tok, CloneBoundVar(pat.Var));
      } else if (pat.Arguments == null) {
        return new CasePattern(pat.tok, pat.Id, null);
      } else {
        return new CasePattern(pat.tok, pat.Id, pat.Arguments.ConvertAll(CloneCasePattern));
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
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        if (d is ArbitraryTypeDecl) {
          // nothing to do
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
    }

    public void ResolveTopLevelDecls_Meat(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies));
      Contract.Requires(cce.NonNullElements(codatatypeDependencies));

      int prevErrorCount = ErrorCount;

      // Resolve the meat of classes, and the type parameters of all top-level type declarations
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          ResolveIterator(iter);
          ResolveClassMemberBodies(iter);  // resolve the automatically generated members

        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          ResolveAttributes(cl.Attributes, false, new NoContext(cl.Module));
          ResolveClassMemberBodies(cl);
        }
        allTypeParameters.PopMarker();
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
            foreach (var tp in iter.TypeArgs) {
              if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                foreach (var p in iter.Ins) {
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    goto DONE;
                  }
                }
                foreach (var p in iter.Outs) {
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    goto DONE;
                  }
                }
              DONE: ;
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
                  foreach (var tp in m.TypeArgs) {
                    if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                      // here's our chance to infer the need for equality support
                      foreach (var p in m.Ins) {
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          goto DONE;
                        }
                      }
                      foreach (var p in m.Outs) {
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          goto DONE;
                        }
                      }
                    DONE: ;
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
        if (!m.IsTailRecursive && m.Body != null && Contract.Exists(m.Decreases.Expressions, e => e is WildcardExpr)) {
          Error(m.Decreases.Expressions[0].tok, "'decreases *' is allowed only on tail-recursive methods");
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
              if (bv.Type.Normalize() is TypeProxy) {
                Error(bv.tok, "type of bound variable '{0}' could not determined; please specify the type explicitly", bv.Name);
              }
            }
          }
        }
        if (CheckTypeIsDetermined(expr.tok, expr.Type, "expression")) {
          var bin = expr as BinaryExpr;
          if (bin != null) {
            bin.ResolvedOp = ResolveOp(bin.Op, bin.E1.Type);
          }
        }
      }
      bool CheckTypeIsDetermined(IToken tok, Type t, string what) {
        Contract.Requires(tok != null);
        Contract.Requires(t != null);
        Contract.Requires(what != null);
        t = t.Normalize();
        if (t is TypeProxy && !(t is InferredTypeProxy || t is ParamTypeProxy || t is ObjectTypeProxy)) {
          Error(tok, "the type of this {0} is underspecified, but it cannot be an arbitrary type.", what);
          return false;
        }
        return true;
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
        var status = CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
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
        } else if (expr is UnaryExpr) {
          var e = (UnaryExpr)expr;
          if (e.Op == UnaryExpr.Opcode.Not) {
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
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          // don't recurse on the specification parts, which are ghost
          if (s.Guard != null) {
            Visit(s.Guard, st);
          }
          Visit(s.Body, st);
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
          Contract.Assert(s.Method.TypeArgs.Count <= s.TypeArgumentSubstitutions.Count);
          var i = 0;
          foreach (var formalTypeArg in s.Method.TypeArgs) {
            var actualTypeArg = s.TypeArgumentSubstitutions[formalTypeArg];
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
        }
        return true;
      }
      protected override bool VisitOneExpr(Expression expr, ref bool st) {
        if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          var t0 = e.E0.Type.Normalize();
          var t1 = e.E1.Type.Normalize();
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
        }
        return true;
      }

      public void CheckEqualityTypes_Type(IToken tok, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(type != null);
        type = type.Normalize();
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
          if (udt.ResolvedClass != null) {
            Contract.Assert(udt.ResolvedClass.TypeArgs.Count == udt.TypeArgs.Count);
            var i = 0;
            foreach (var argType in udt.TypeArgs) {
              var formalTypeArg = udt.ResolvedClass.TypeArgs[i];
              if (formalTypeArg.MustSupportEquality && !argType.SupportsEquality) {
                Error(tok, "type parameter {0} ({1}) passed to type {2} must support equality (got {3}){4}", i, formalTypeArg.Name, udt.ResolvedClass.Name, argType, TypeEqualityErrorMessageHint(argType));
              }
              CheckEqualityTypes_Type(tok, argType);
              i++;
            }
          } else {
            Contract.Assert(udt.TypeArgs.Count == 0);  // TypeParameters have no type arguments
          }

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

      type = type.Normalize();
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
        if (udt.ResolvedClass != null) {
          var i = 0;
          foreach (var argType in udt.TypeArgs) {
            var formalTypeArg = udt.ResolvedClass.TypeArgs[i];
            if ((formalTypeArg.MustSupportEquality && argType.AsTypeParameter == tp) || InferRequiredEqualitySupport(tp, argType)) {
              return true;
            }
            i++;
          }
        } else {
          Contract.Assert(udt.TypeArgs.Count == 0);  // TypeParameters have no type arguments
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
    void ResolveClassMemberTypes(ClassDecl/*!*/ cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        member.EnclosingClass = cl;
        if (member is Field) {
          ResolveType(member.tok, ((Field)member).Type, ResolveTypeOption.DontInfer, null);

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
          ResolveAttributes(member.Attributes, false, new NoContext(currentClass.Module));
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

    void AddDatatypeDependencyEdge(IndDatatypeDecl/*!*/ dt, Type/*!*/ tp, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(tp != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

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
            if (arg.IsGhost || (anotherIndDt != null && anotherIndDt.EqualitySupport == IndDatatypeDecl.ES.Never) || arg.Type.IsCoDatatype) {
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
                var otherUdt = (UserDefinedType)arg.Type.Normalize();
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
                var otherUdt = (UserDefinedType)arg.Type.Normalize();
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

    void ResolveAttributes(Attributes attrs, bool twoState, ICodeContext codeContext) {
      // order does not matter much for resolution, so resolve them in reverse order
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Args != null) {
          ResolveAttributeArgs(attrs.Args, twoState, codeContext, true);
        }
      }
    }

    void ResolveAttributeArgs(List<Attributes.Argument/*!*/>/*!*/ args, bool twoState, ICodeContext codeContext, bool allowGhosts) {
      Contract.Requires(args != null);
      foreach (Attributes.Argument aa in args) {
        Contract.Assert(aa != null);
        if (aa.E != null) {
          ResolveExpression(aa.E, twoState, codeContext);
          if (!allowGhosts) {
            CheckIsNonGhost(aa.E);
          }
        }
      }
    }

    void ResolveTypeParameters(List<TypeParameter/*!*/>/*!*/ tparams, bool emitErrors, TypeParameter.ParentType/*!*/ parent) {
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push non-duplicated type parameter names
      int index = 0;
      foreach (TypeParameter tp in tparams) {
        Contract.Assert(tp != null);
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
      var option = f.TypeArgs.Count == 0 ? ResolveTypeOption.AllowPrefixExtend : ResolveTypeOption.AllowPrefix;
      foreach (Formal p in f.Formals) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, option, f.TypeArgs);
      }
      ResolveType(f.tok, f.ResultType, option, f.TypeArgs);
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
      ResolveAttributes(f.Attributes, false, f);
      foreach (Expression r in f.Req) {
        ResolveExpression(r, false, f);
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Precondition must be a boolean (got {0})", r.Type);
        }
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, "reads", f.IsGhost, f);
      }
      foreach (Expression r in f.Ens) {
        ResolveExpression(r, false, f);  // since this is a function, the postcondition is still a one-state predicate
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Postcondition must be a boolean (got {0})", r.Type);
        }
      }
      ResolveAttributes(f.Decreases.Attributes, false, f);
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, false, f);
        // any type is fine
      }
      if (f.Body != null) {
        var prevErrorCount = ErrorCount;
        ResolveExpression(f.Body, false, f);
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

    void ResolveFrameExpression(FrameExpression fe, string kind, bool isGhostContext, ICodeContext codeContext) {
      Contract.Requires(fe != null);
      Contract.Requires(kind != null);
      Contract.Requires(codeContext != null);
      ResolveExpression(fe.E, false, codeContext);
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      if (t is CollectionType) {
        t = ((CollectionType)t).Arg;
      }
      if (!UnifyTypes(t, new ObjectTypeProxy())) {
        Error(fe.E, "a {0}-clause expression must denote an object or a collection of objects (instead got {1})", kind, fe.E.Type);
      } else if (fe.FieldName != null) {
        NonProxyType nptype;
        MemberDecl member = ResolveMember(fe.E.tok, t, fe.FieldName, out nptype);
        UserDefinedType ctype = (UserDefinedType)nptype;  // correctness of cast follows from the DenotesClass test above
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          Error(fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, ctype.Name);
        } else if (isGhostContext && !member.IsGhost) {
          Error(fe.E, "in a ghost context, only ghost fields can be mentioned as frame targets ({0})", fe.FieldName);
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
      var option = m.TypeArgs.Count == 0 ? ResolveTypeOption.AllowPrefixExtend : ResolveTypeOption.AllowPrefix;
      // resolve in-parameters
      foreach (Formal p in m.Ins) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, option, m.TypeArgs);
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.tok, p.Type, option, m.TypeArgs);
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
          ResolveAttributes(e.Attributes, false, m);
          ResolveExpression(e.E, false, m);
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.E.Type, Type.Bool)) {
            Error(e.E, "Precondition must be a boolean (got {0})", e.E.Type);
          }
        }
        ResolveAttributes(m.Mod.Attributes, false, m);
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, "modifies", m.IsGhost, m);
          if (m is Lemma) {
            Error(fe.tok, "lemmas are not allowed to have modifies clauses");
          } else if (m is CoLemma) {
            Error(fe.tok, "colemmas are not allowed to have modifies clauses");
          }
        }
        ResolveAttributes(m.Decreases.Attributes, false, m);
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, false, m);
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
          ResolveAttributes(e.Attributes, true, m);
          ResolveExpression(e.E, true, m);
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
        ResolveAttributes(m.Attributes, false, m);

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
      Contract.Requires(dtTypeArguments != null);
      foreach (Formal p in ctor.Formals) {
        ResolveType(p.tok, p.Type, ResolveTypeOption.AllowExact, dtTypeArguments);
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
      var option = iter.TypeArgs.Count == 0 ? ResolveTypeOption.AllowPrefixExtend : ResolveTypeOption.AllowPrefix;
      // resolve the types of the parameters
      foreach (var p in iter.Ins.Concat(iter.Outs)) {
        ResolveType(p.tok, p.Type, option, iter.TypeArgs);
      }
      // resolve the types of the added fields (in case some of these types would cause the addition of default type arguments)
      foreach (var p in iter.OutsHistoryFields) {
        ResolveType(p.tok, p.Type, option, iter.TypeArgs);
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
        ResolveExpression(e, false, iter);
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        if (!UnifyTypes(d.Type, e.Type)) {
          // bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
          Error(e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
        }
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, "reads", false, iter);
      }
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, "modifies", false, iter);
      }
      foreach (MaybeFreeExpression e in iter.Requires) {
        ResolveExpression(e.E, false, iter);
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
        ResolveExpression(e.E, false, iter);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Yield precondition must be a boolean (got {0})", e.E.Type);
        }
      }
      foreach (MaybeFreeExpression e in iter.YieldEnsures) {
        ResolveExpression(e.E, true, iter);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Yield postcondition must be a boolean (got {0})", e.E.Type);
        }
      }
      foreach (MaybeFreeExpression e in iter.Ensures) {
        ResolveExpression(e.E, true, iter);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Postcondition must be a boolean (got {0})", e.E.Type);
        }
      }

      ResolveAttributes(iter.Attributes, false, iter);

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
          new FieldSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new IdentifierExpr(p.tok, p.Name))));
      }
      foreach (var p in iter.OutsHistoryFields) {
        // ensures this.ys == [];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new FieldSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new SeqDisplayExpr(p.tok, new List<Expression>()))));
      }
      // ensures this.Valid();
      ens.Add(new MaybeFreeExpression(new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>())));
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
        new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"),
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
        new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"),
        new OldExpr(iter.tok, frameSet))));
      // ensures this._new == {};
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
        new SetDisplayExpr(iter.tok, new List<Expression>()))));
      // ensures this._decreases0 == old(DecreasesClause[0]) && ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
          new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), iter.DecreasesFields[i].Name),
          new OldExpr(iter.tok, p))));
      }

      // ---------- here comes predicate Valid() ----------
      var reads = iter.Member_Valid.Reads;
      reads.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));  // reads this;
      reads.Add(new FrameExpression(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"), null));  // reads this._reads;
      reads.Add(new FrameExpression(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));  // reads this._new;

      // ---------- here comes method MoveNext() ----------
      // requires this.Valid();
      var req = iter.Member_MoveNext.Req;
      req.Add(new MaybeFreeExpression(new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>())));
      // requires YieldRequires;
      req.AddRange(iter.YieldRequires);
      // modifies this, this._modifies, this._new;
      var mod = iter.Member_MoveNext.Mod.Expressions;
      mod.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));
      mod.Add(new FrameExpression(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"), null));
      mod.Add(new FrameExpression(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));
      // ensures fresh(_new - old(_new));
      ens = iter.Member_MoveNext.Ens;
      ens.Add(new MaybeFreeExpression(new FreshExpr(iter.tok,
        new BinaryExpr(iter.tok, BinaryExpr.Opcode.Sub,
          new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
          new OldExpr(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))))));
      // ensures more ==> this.Valid();
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
        new IdentifierExpr(iter.tok, "more"),
        new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>()))));
      // ensures this.ys == if more then old(this.ys) + [this.y] else old(this.ys);
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var ite = new ITEExpr(iter.tok, new IdentifierExpr(iter.tok, "more"),
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add,
            new OldExpr(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)),
            new SeqDisplayExpr(iter.tok, new List<Expression>() { new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), y.Name) })),
          new OldExpr(iter.tok, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)));
        var eq = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq, new FieldSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name), ite);
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
          new UnaryExpr(iter.tok, UnaryExpr.Opcode.Not, new IdentifierExpr(iter.tok, "more")),
          e.E),
          e.IsFree));
      }
      // decreases this._decreases0, this._decreases1, ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        iter.Member_MoveNext.Decreases.Expressions.Add(new FieldSelectExpr(p.tok, new ThisExpr(p.tok), iter.DecreasesFields[i].Name));
      }
      iter.Member_MoveNext.Decreases.Attributes = iter.Decreases.Attributes;
    }

    /// <summary>
    /// If ResolveType/ResolveTypeLenient encounters a (datatype or class) type "C" with no supplied arguments, then
    /// the ResolveTypeOption says what to do.  The last three options take a List as a parameter, which (would have
    /// been supplied as an argument if C# had datatypes instead of just enums, but since C# doesn't) is supplied
    /// as another parameter (called 'defaultTypeArguments') to ResolveType/ResolveTypeLenient.
    /// </summary>
    public enum ResolveTypeOption
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
      /// if exactly defaultTypeArguments.Count type arguments are needed, use defaultTypeArguments
      /// </summary>
      AllowExact,
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
    public void ResolveType(IToken tok, Type type, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires((option == ResolveTypeOption.DontInfer || option == ResolveTypeOption.InferTypeProxies) == (defaultTypeArguments == null));
      var r = ResolveTypeLenient(tok, type, option, defaultTypeArguments, false);
      Contract.Assert(r == null);
    }

    public class ResolveTypeReturn
    {
      public readonly Type ReplacementType;
      public readonly string LastName;
      public readonly IToken LastToken;
      public ResolveTypeReturn(Type replacementType, string lastName, IToken lastToken) {
        Contract.Requires(replacementType != null);
        Contract.Requires(lastName != null);
        Contract.Requires(lastToken != null);
        ReplacementType = replacementType;
        LastName = lastName;
        LastToken = lastToken;
      }
    }
    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// One more thing:  if "allowShortenedPath" is true, then if the resolution would have produced
    ///   an error message that could have been avoided if "type" denoted an identifier sequence one
    ///   shorter, then return an unresolved replacement type where the identifier sequence is one
    ///   shorter.  (In all other cases, the method returns null.)
    /// </summary>
    public ResolveTypeReturn ResolveTypeLenient(IToken tok, Type type, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments, bool allowShortenedPath) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires((option == ResolveTypeOption.DontInfer || option == ResolveTypeOption.InferTypeProxies) == (defaultTypeArguments == null));
      if (type is BasicType) {
        // nothing to resolve
      } else if (type is MapType) {
        var mt = (MapType)type;
        int typeArgumentCount = 0;
        if (mt.HasTypeArg()) {
          ResolveType(tok, mt.Domain, option, defaultTypeArguments);
          ResolveType(tok, mt.Range, option, defaultTypeArguments);
          typeArgumentCount = 2;
        } else if (option != ResolveTypeOption.DontInfer) {
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

        if (mt.Domain.IsSubrangeType || mt.Range.IsSubrangeType) {
          Error(tok, "sorry, cannot instantiate collection type with a subrange type");
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        if (t.HasTypeArg()) {
          ResolveType(tok, t.Arg, option, defaultTypeArguments);
        } else if (option != ResolveTypeOption.DontInfer) {
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

        if (t.Arg.IsSubrangeType) {
          Error(tok, "sorry, cannot instantiate collection type with a subrange type");
        }
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        foreach (Type tt in t.TypeArgs) {
          ResolveType(t.tok, tt, option, defaultTypeArguments);
          if (tt.IsSubrangeType) {
            Error(t.tok, "sorry, cannot instantiate type parameter with a subrange type");
          }
        }
        TypeParameter tp = t.Path.Count == 0 ? allTypeParameters.Find(t.Name) : null;
        if (tp != null) {
          if (t.TypeArgs.Count == 0) {
            t.ResolvedParam = tp;
          } else {
            Error(t.tok, "Type parameter expects no type arguments: {0}", t.Name);
          }
        } else if (t.ResolvedClass == null) {  // this test is because 'array' is already resolved; TODO: an alternative would be to pre-populate 'classes' with built-in references types like 'array' (and perhaps in the future 'string')
          TopLevelDecl d = null;

          int j;
          var sig = moduleInfo;
          for (j = 0; j < t.Path.Count; j++) {
            ModuleSignature submodule;
            if (sig.FindSubmodule(t.Path[j].val, out submodule)) {
              sig = GetSignature(submodule);
            } else {
              // maybe the last component of t.Path is actually the type name
              if (allowShortenedPath && t.TypeArgs.Count == 0 && j == t.Path.Count - 1 && sig.TopLevels.TryGetValue(t.Path[j].val, out d)) {
                // move the last component of t.Path to t.tok/t.name, tell the caller about this, and continue
                var reducedPath = new List<IToken>();
                for (int i = 0; i < j; i++) {
                  reducedPath.Add(t.Path[i]);
                }
                return new ResolveTypeReturn(new UserDefinedType(t.Path[j], t.Path[j].val, t.TypeArgs, reducedPath), t.Name, t.tok);
              } else {
                Error(t.Path[j], ModuleNotFoundErrorMessage(j, t.Path));
              }
              break;
            }
          }
          if (j == t.Path.Count) {
            if (!sig.TopLevels.TryGetValue(t.Name, out d)) {
              if (j == 0)
                Error(t.tok, "Undeclared top-level type or type parameter: {0} (did you forget to qualify a name?)", t.Name);
              else
                Error(t.tok, "Undeclared type {0} in module {1}", t.Name, t.Path[t.Path.Count - 1].val);
            }
          } else {
            // error has already been reported
          }

          if (d == null) {
            // error has been reported above
          } else if (d is AmbiguousTopLevelDecl) {
            Error(t.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", t.Name, ((AmbiguousTopLevelDecl)d).ModuleNames());
          } else if (d is ArbitraryTypeDecl) {
            t.ResolvedParam = ((ArbitraryTypeDecl)d).TheType;  // resolve like a type parameter
          } else {
            // d is a class or datatype, and it may have type parameters
            t.ResolvedClass = d;
            if (option == ResolveTypeOption.DontInfer) {
              // don't add anything
            } else if (d.TypeArgs.Count != t.TypeArgs.Count && t.TypeArgs.Count == 0) {
              FillInTypeArguments(t.tok, d.TypeArgs.Count, t.TypeArgs, defaultTypeArguments, option);
            }
            // defaults and auto have been applied; check if we now have the right number of arguments
            if (d.TypeArgs.Count != t.TypeArgs.Count) {
              Error(t.tok, "Wrong number of type arguments ({0} instead of {1}) passed to class/datatype: {2}", t.TypeArgs.Count, d.TypeArgs.Count, t.Name);
            }
          }
        }

      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(tok, t.T, option, defaultTypeArguments);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return null;
    }

    /// <summary>
    /// Adds to "typeArgs" a list of "n" type arguments, possibly extending "defaultTypeArguments".
    /// </summary>
    static void FillInTypeArguments(IToken tok, int n, List<Type> typeArgs, List<TypeParameter> defaultTypeArguments, ResolveTypeOption option) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      Contract.Requires(typeArgs != null && typeArgs.Count == 0);
      if (option == ResolveTypeOption.InferTypeProxies) {
        // add type arguments that will be inferred
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new InferredTypeProxy());
        }
      } else if (option == ResolveTypeOption.AllowExact && defaultTypeArguments.Count != n) {
        // the number of default arguments is not exactly what we need, so don't add anything
      } else if (option == ResolveTypeOption.AllowPrefix && defaultTypeArguments.Count < n) {
        // there aren't enough default arguments, so don't do anything
      } else {
        // we'll add arguments
        if (option == ResolveTypeOption.AllowPrefixExtend) {
          // extend defaultTypeArguments, if needed
          for (int i = defaultTypeArguments.Count; i < n; i++) {
            defaultTypeArguments.Add(new TypeParameter(tok, "_T" + i));
          }
        }
        Contract.Assert(n <= defaultTypeArguments.Count);
        // automatically supply a prefix of the arguments from defaultTypeArguments
        for (int i = 0; i < n; i++) {
          var typeArg = new UserDefinedType(tok, defaultTypeArguments[i].Name, new List<Type>(), null);
          typeArg.ResolvedParam = defaultTypeArguments[i];  // resolve "typeArg" here
          typeArgs.Add(typeArg);
        }
      }
    }

    public bool UnifyTypes(Type a, Type b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      while (a is TypeProxy) {
        TypeProxy proxy = (TypeProxy)a;
        if (proxy.T == null) {
          // merge a and b; to avoid cycles, first get to the bottom of b
          while (b is TypeProxy && ((TypeProxy)b).T != null) {
            b = ((TypeProxy)b).T;
          }
          return AssignProxy(proxy, b);
        } else {
          a = proxy.T;
        }
      }

      while (b is TypeProxy) {
        TypeProxy proxy = (TypeProxy)b;
        if (proxy.T == null) {
          // merge a and b (we have already got to the bottom of a)
          return AssignProxy(proxy, a);
        } else {
          b = proxy.T;
        }
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
        return b is MapType && UnifyTypes(((MapType)a).Domain, ((MapType)b).Domain) && UnifyTypes(((MapType)a).Range, ((MapType)b).Range);
      } else if (a is SeqType) {
        return b is SeqType && UnifyTypes(((SeqType)a).Arg, ((SeqType)b).Arg);
      } else if (a is UserDefinedType) {
        if (!(b is UserDefinedType)) {
          return false;
        }
        UserDefinedType aa = (UserDefinedType)a;
        UserDefinedType bb = (UserDefinedType)b;
        if (aa.ResolvedClass != null && aa.ResolvedClass == bb.ResolvedClass) {
          // these are both resolved class/datatype types
          Contract.Assert(aa.TypeArgs.Count == bb.TypeArgs.Count);
          bool successSoFar = true;
          for (int i = 0; i < aa.TypeArgs.Count; i++) {
            if (!UnifyTypes(aa.TypeArgs[i], bb.TypeArgs[i])) {
              successSoFar = false;
            }
          }
          return successSoFar;
        } else if (aa.ResolvedParam != null && aa.ResolvedParam == bb.ResolvedParam) {
          // these are both resolved type parameters
          Contract.Assert(aa.TypeArgs.Count == 0 && bb.TypeArgs.Count == 0);
          return true;
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
        if (!dtp.Co && t.IsIndDatatype) {
          // all is fine, proxy can be redirected to t
        } else if (dtp.Co && t.IsCoDatatype) {
          // all is fine, proxy can be redirected to t
        } else {
          return false;
        }

      } else if (proxy is ObjectTypeProxy) {
        if (t is ObjectType || UserDefinedType.DenotesClass(t) != null) {
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
        OperationTypeProxy opProxy = (OperationTypeProxy)proxy;
        if (t is IntType || t is RealType || t is SetType || t is MultiSetType || (opProxy.AllowSeq && t is SeqType)) {
          // this is the expected case
        } else {
          return false;
        }

      } else if (proxy is IndexableTypeProxy) {
        var iProxy = (IndexableTypeProxy)proxy;
        if (t is SeqType) {
          if (!UnifyTypes(iProxy.Domain, Type.Int)) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, ((SeqType)t).Arg)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Range)) {
            return false;
          }
        } else if (iProxy.AllowArray && t.IsArrayType && (t.AsArrayType).Dims == 1) {
          Type elType = UserDefinedType.ArrayElementType(t);
          if (!UnifyTypes(iProxy.Domain, Type.Int)) {
            return false;
          } else if (!UnifyTypes(iProxy.Range, elType)) {
            return false;
          } else if (!UnifyTypes(iProxy.Arg, iProxy.Range)) {
            return false;
          }
        } else if (t is MapType) {
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
          } else if (!UnifyTypes(iProxy.Range, Type.Int)) {
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
        proxy.T = t;
      }
      return true;
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
          a.T = builtIns.ArrayType(1, ib.Arg);
          b.T = a.T;
          return UnifyTypes(ib.Arg, ib.Range);
        } else {
          return false;
        }

      } else if (a is CollectionTypeProxy) {
        if (b is CollectionTypeProxy) {
          a.T = b;
          return UnifyTypes(((CollectionTypeProxy)a).Arg, ((CollectionTypeProxy)b).Arg);
        } else if (b is OperationTypeProxy) {
          if (((OperationTypeProxy)b).AllowSeq) {
            b.T = a;  // a is a stronger constraint than b
          } else {
            // a says set<T>,seq<T> and b says int,set; the intersection is set<T>
            a.T = new SetType(((CollectionTypeProxy)a).Arg);
            b.T = a.T;
          }
          return true;
        } else if (b is IndexableTypeProxy) {
          CollectionTypeProxy pa = (CollectionTypeProxy)a;
          var ib = (IndexableTypeProxy)b;
          // pa is:
          //   set(Arg) or multiset(Arg) or seq(Arg) or map(Arg, anyRange)
          // pb is:
          //   seq(Arg) or multiset(Arg) or map(Domain, Arg), or
          //   if AllowArray, array(Arg)
          // Their intersection is:
          if (ib.AllowArray) {
            var c = new IndexableTypeProxy(ib.Domain, ib.Range, ib.Arg, false);
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
          if (pa.AllowSeq) {
            a.T = b;  // a has the weaker requirement
          } else {
            b.T = a;  // a has the stronger requirement
          }
          return true;
        } else {
          var pb = (IndexableTypeProxy)b;  // cast justification:  else we have unexpected restricted-proxy type
          // a is:  int or set or multiset or seq
          // b is:  seq, multiset, map, or possibly array
          if (!pa.AllowSeq) {
            // strengthen a and b to a multiset type
            b.T = new MultiSetType(pb.Arg);
            a.T = b.T;
            return true;
          } else {
            // strengthen a and b to a sequence type
            b.T = new SeqType(pb.Arg);  // TODO: the type is really *either* a seq or a multiset
            a.T = b.T;
            return true;
          }
        }

      } else if (a is IndexableTypeProxy) {
        var ia = (IndexableTypeProxy)a;
        var ib = (IndexableTypeProxy)b;  // cast justification: else we have unexpected restricted-proxy type
        if (ia.AllowArray) {
          a.T = b;  // a has the weaker requirement
        } else {
          b.T = a;  // a has the strong requirement
        }
        return UnifyTypes(ia.Domain, ib.Domain) && UnifyTypes(ia.Range, ib.Range) && UnifyTypes(ia.Arg, ib.Arg);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
      }
    }

    /// <summary>
    /// "specContextOnly" means that the statement must be erasable, that is, it should be okay to omit it
    /// at run time.  That means it must not have any side effects on non-ghost variables, for example.
    /// </summary>
    public void ResolveStatement(Statement stmt, bool specContextOnly, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      ResolveAttributes(stmt.Attributes, true, codeContext);
      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        ResolveAttributes(s.Attributes, false, codeContext);
        s.IsGhost = true;
        ResolveExpression(s.Expr, true, codeContext);
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Expr.Type, Type.Bool)) {
          Error(s.Expr, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Expr.Type);
        }

      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        ResolveAttributeArgs(s.Args, false, codeContext, false);
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
          } else if (cmc.Outs.Count != s.rhss.Count)
            Error(s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.rhss.Count, cmc.Outs.Count, kind);
          else {
            Contract.Assert(s.rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            int i = 0;
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
                var yieldIdent = new FieldSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, true, codeContext);
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
              // link the receiver parameter properly:
              if (s.rhss[i] is TypeRhs) {
                var r = (TypeRhs)s.rhss[i];
                if (r.Arguments != null) {
                  r.ReceiverArgumentForInitCall = produceLhs;
                }
              }
              i++;
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
          ResolveType(local.Tok, local.OptionalType, ResolveTypeOption.InferTypeProxies, null);
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
          // there is one more place where a newly declared local may be lurking
          if (upd.Rhss.Count == 1 && upd.Rhss[0] is TypeRhs) {
            var rhs = (TypeRhs)upd.Rhss[0];
            Contract.Assert(s.Locals.Count != 0);  // this is always true of a VarDeclStmt
            var local = s.Locals[0];
            if (rhs != null && rhs.ReceiverArgumentForInitCall != null) {
              var lhs = (IdentifierExpr)rhs.ReceiverArgumentForInitCall;  // as above, we expect this to be an IdentifierExpr, because that's how the parser sets things up
              Contract.Assert(lhs.Type == null || (upd.Lhss.Count == 1 && upd.Lhss[0] == lhs));  // if it's been resolved before, it's because it's aliased with a Lhss
              lhs.Var = local;
              lhs.Type = local.type;
            }
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
            if (!(local.Type is BoolType))
            {
              Error(s, "assumption variable must be of type 'bool'");
            }
          }
        }

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Lhs, true, codeContext);  // allow ghosts for now, tighted up below
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
            CheckIsLvalue(lhs);
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
        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          if (fse.Field != null) {  // otherwise, an error was reported above
            lvalueIsGhost = fse.Field.IsGhost;
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
            CheckIsLvalue(fse);
          }
        } else if (lhs is SeqSelectExpr) {
          var slhs = (SeqSelectExpr)lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(slhs.Seq.Type != null);
            if (specContextOnly) {
              Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
            }
            CheckIsLvalue(slhs);
          }

        } else if (lhs is MultiSelectExpr) {
          if (specContextOnly) {
            Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          }
          CheckIsLvalue(lhs);

        } else {
          CheckIsLvalue(lhs);
        }

        s.IsGhost = lvalueIsGhost;
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, true, codeContext);
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
          ResolveExpression(s.Guard, true, codeContext);
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
        if (s.Guard != null) {
          int prevErrorCount = ErrorCount;
          ResolveExpression(s.Guard, true, codeContext);
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          bool successfullyResolved = ErrorCount == prevErrorCount;
          if (!UnifyTypes(s.Guard.Type, Type.Bool)) {
            Error(s.Guard, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Guard.Type);
          }
          if (!specContextOnly && successfullyResolved) {
            bodyMustBeSpecOnly = UsesSpecFeatures(s.Guard);
          }
        }

        foreach (MaybeFreeExpression inv in s.Invariants) {
          ResolveAttributes(inv.Attributes, true, codeContext);
          ResolveExpression(inv.E, true, codeContext);
          Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(inv.E.Type, Type.Bool)) {
            Error(inv.E, "invariant is expected to be of type {0}, but is {1}", Type.Bool, inv.E.Type);
          }
        }

        ResolveAttributes(s.Decreases.Attributes, true, codeContext);
        foreach (Expression e in s.Decreases.Expressions) {
          ResolveExpression(e, true, codeContext);
          if (bodyMustBeSpecOnly && e is WildcardExpr) {
            Error(e, "'decreases *' is not allowed on ghost loops");
          }
          // any type is fine
        }

        if (s.Mod.Expressions != null) {
          ResolveAttributes(s.Mod.Attributes, true, codeContext);
          foreach (FrameExpression fe in s.Mod.Expressions) {
            ResolveFrameExpression(fe, "modifies", bodyMustBeSpecOnly, codeContext);
          }
        }
        s.IsGhost = bodyMustBeSpecOnly;
        loopStack.Add(s);  // push
        if (s.Labels == null) {  // otherwise, "s" is already in "inSpecOnlyContext" map
          inSpecOnlyContext.Add(s, specContextOnly);
        }

        ResolveStatement(s.Body, bodyMustBeSpecOnly, codeContext);
        loopStack.RemoveAt(loopStack.Count - 1);  // pop

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        s.IsGhost = ResolveAlternatives(s.Alternatives, specContextOnly, s, codeContext);
        foreach (MaybeFreeExpression inv in s.Invariants) {
          ResolveExpression(inv.E, true, codeContext);
          Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(inv.E.Type, Type.Bool)) {
            Error(inv.E, "invariant is expected to be of type {0}, but is {1}", Type.Bool, inv.E.Type);
          }
        }

        foreach (Expression e in s.Decreases.Expressions) {
          ResolveExpression(e, true, codeContext);
          if (s.IsGhost && e is WildcardExpr) {
            Error(e, "'decreases *' is not allowed on ghost loops");
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
          ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, true, codeContext);
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Range.Type, Type.Bool)) {
          Error(stmt, "range restriction in forall statement must be of type bool (instead got {0})", s.Range.Type);
        }
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, true, codeContext);
          Contract.Assert(ens.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(ens.E.Type, Type.Bool)) {
            Error(ens.E, "ensures condition is expected to be of type {0}, but is {1}", Type.Bool, ens.E.Type);
          }
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s.Attributes, true, codeContext);

        bool bodyMustBeSpecOnly = specContextOnly || (prevErrorCount == ErrorCount && UsesSpecFeatures(s.Range));
        if (!bodyMustBeSpecOnly && prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(s.Range);  // we need to resolve operators before the call to DiscoverBounds
          s.Bounds = DiscoverBounds(s.Tok, s.BoundVars, s.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            bodyMustBeSpecOnly = true;
          }
        }
        s.IsGhost = bodyMustBeSpecOnly;

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
        ResolveAttributes(s.Mod.Attributes, true, codeContext);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          // (yes, say "modifies", not "modify", in the next line -- it seems to give a more readable error message
          ResolveFrameExpression(fe, "modifies", specContextOnly, codeContext);
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
          ResolveExpression(e0, true, codeContext);
          Contract.Assert(e0.Type != null);  // follows from postcondition of ResolveExpression
          for (int i = 1; i < s.Lines.Count; i++) {
            if (i < s.Lines.Count - 1 || prevErrorCount == ErrorCount) { // do not resolve the dummy step if there were errors, it might generate more errors
              var e1 = s.Lines[i];
              ResolveExpression(e1, true, codeContext);
              Contract.Assert(e1.Type != null);  // follows from postcondition of ResolveExpression
              if (!UnifyTypes(e0.Type, e1.Type)) {
                Error(e1, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, e0.Type);
              } else {
                var step = s.StepOps[i - 1].StepExpr(e0, e1); // Use custom line operator
                ResolveExpression(step, true, codeContext);
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
        ResolveExpression(s.Result, true, codeContext);
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != ErrorCount || s.Steps.Count == s.Hints.Count);

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        bool bodyIsSpecOnly = specContextOnly;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Source, true, codeContext);
        Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = ErrorCount == prevErrorCount;
        if (!specContextOnly && successfullyResolved) {
          bodyIsSpecOnly = UsesSpecFeatures(s.Source);
        }
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        Dictionary<TypeParameter, Type> subst = new Dictionary<TypeParameter, Type>();
        if (s.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)s.Source.Type;
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
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
            ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
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
                guess = Expression.CreateSubtract(bin.E1, bin.E0);
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
              case BinaryExpr.ResolvedOpcode.Gt:
                // for A >= B and A > B, use the decreases A - B
                guess = Expression.CreateSubtract(bin.E0, bin.E1);
                break;
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                if (bin.E0.Type is IntType || bin.E0.Type is RealType) {
                  // for A != B where A and B are integers, use the absolute difference between A and B (that is: if A <= B then B-A else A-B)
                  var AminusB = Expression.CreateSubtract(bin.E0, bin.E1);
                  var BminusA = Expression.CreateSubtract(bin.E1, bin.E0);
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
        ResolveExpression(lhs, true, codeContext);
        if (ec == ErrorCount) {
          if (update == null && specContextOnly && !AssignStmt.LhsIsToGhost(lhs) && !codeContext.IsGhost) {
            Error(lhs, "cannot assign to non-ghost variable in a ghost context");
          }
          if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
            Error(lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
          }
          var ie = lhs.Resolved as IdentifierExpr;
          if (ie != null) {
            if (lhsNameSet.Contains(ie.Name)) {
              Error(update, "duplicate variable in left-hand side of call statement: {0}", ie.Name);
            } else {
              lhsNameSet.Add(ie.Name);
            }
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
      CallRhs callRhs = null;
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is TypeRhs) {
          var tr = (TypeRhs)rhs;
          ResolveTypeRhs(tr, update, specContextOnly, codeContext);
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else if (rhs is CallRhs) {
          // (a CallRhs is never parsed; we must have got here from an act of cloning)
          isEffectful = true;
          callRhs = callRhs ?? (CallRhs)rhs;
        } else {
          var er = (ExprRhs)rhs;
          if (er.Expr is IdentifierSequence) {
            var cRhs = ResolveIdentifierSequence((IdentifierSequence)er.Expr, true, codeContext, true);
            isEffectful = cRhs != null;
            callRhs = callRhs ?? cRhs;
          } else if (er.Expr is FunctionCallExpr) {
            var cRhs = ResolveFunctionCallExpr((FunctionCallExpr)er.Expr, true, codeContext, true);
            isEffectful = cRhs != null;
            callRhs = callRhs ?? cRhs;
          } else {
            ResolveExpression(er.Expr, true, codeContext);
            isEffectful = false;
          }
        }
        if (isEffectful && firstEffectfulRhs == null) {
          firstEffectfulRhs = rhs.Tok;
        }
      }

      // figure out what kind of UpdateStmt this is
      if (firstEffectfulRhs == null) {
        if (update.Lhss.Count == 0) {
          Contract.Assert(update.Rhss.Count == 1);  // guaranteed by the parser
          Error(update, "expected method call, found expression");
        } else if (update.Lhss.Count != update.Rhss.Count) {
          Error(update, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", update.Lhss.Count, update.Rhss.Count);
        } else if (ErrorCount == errorCountBeforeCheckingLhs) {
          // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translated properly as multi-assignment)
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
          if (callRhs != null) {
            Error(callRhs.Tok, "cannot have method call in return statement.");
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
        } else if (callRhs == null) {
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
          var a = new CallStmt(callRhs.Tok, update.EndTok, resolvedLhss, callRhs.Receiver, callRhs.MethodName, callRhs.Args);
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
      ResolveExpression(s.Expr, true, codeContext);
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
        ResolveExpression(alternative.Guard, true, codeContext);
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

      // resolve receiver
      ResolveReceiver(s.Receiver, true, codeContext);
      Contract.Assert(s.Receiver.Type != null);  // follows from postcondition of ResolveExpression
      if (receiverType == null) {
        receiverType = s.Receiver.Type;
      }
      // resolve the method name
      NonProxyType nptype;
      MemberDecl member = ResolveMember(s.Tok, receiverType, s.MethodName, out nptype);
      Method callee = null;
      if (member == null) {
        // error has already been reported by ResolveMember
      } else if (member is Method) {
        s.Method = (Method)member;
        callee = s.Method;
        if (!isInitCall && callee is Constructor) {
          Error(s, "a constructor is only allowed to be called when an object is being allocated");
        }
        s.IsGhost = callee.IsGhost;
        if (specContextOnly && !callee.IsGhost) {
          Error(s, "only ghost methods can be called from this context");
        }
      } else {
        Error(s, "member {0} in type {1} does not refer to a method", s.MethodName, nptype);
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
        bool allowGhost = s.IsGhost || callee == null || callee.Ins.Count <= j || callee.Ins[j].IsGhost;
        var ec = ErrorCount;
        ResolveExpression(e, true, codeContext);
        if (ec == ErrorCount && !allowGhost) {
          CheckIsNonGhost(e);
        }
        j++;
      }

      if (callee == null) {
        // error has been reported above
      } else if (callee.Ins.Count != s.Args.Count) {
        Error(s, "wrong number of method arguments (got {0}, expected {1})", s.Args.Count, callee.Ins.Count);
      } else if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          Error(s, "a method called as an initialization method must not have any result arguments");
        } else {
          Error(s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
        }
      } else {
        Contract.Assert(nptype != null);  // follows from postcondition of ResolveMember above
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
#if !NO_WORK_TO_BE_DONE
        UserDefinedType ctype = (UserDefinedType)nptype;  // TODO: get rid of this statement, make this code handle any non-proxy type
#endif
        // build the type substitution map
        s.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < ctype.TypeArgs.Count; i++) {
          s.TypeArgumentSubstitutions.Add(cce.NonNull(ctype.ResolvedClass).TypeArgs[i], ctype.TypeArgs[i]);
        }
        foreach (TypeParameter p in callee.TypeArgs) {
          s.TypeArgumentSubstitutions.Add(p, new ParamTypeProxy(p));
        }
        // type check the arguments
        for (int i = 0; i < callee.Ins.Count; i++) {
          Type st = SubstType(callee.Ins[i].Type, s.TypeArgumentSubstitutions);
          if (!UnifyTypes(cce.NonNull(s.Args[i].Type), st)) {
            Error(s, "incorrect type of method in-parameter {0} (expected {1}, got {2})", i, st, s.Args[i].Type);
          }
        }
        for (int i = 0; i < callee.Outs.Count; i++) {
          Type st = SubstType(callee.Outs[i].Type, s.TypeArgumentSubstitutions);
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
              } else if (resolvedLhs is FieldSelectExpr) {
                var ll = (FieldSelectExpr)resolvedLhs;
                if (!ll.Field.IsGhost) {
                  Error(s, "actual out-parameter {0} is required to be a ghost field", i);
                }
              } else {
                // this is an array update, and arrays are always non-ghost
                Error(s, "actual out-parameter {0} is required to be a ghost variable", i);
              }
            }
            // LHS must denote a mutable field.
            CheckIsLvalue(resolvedLhs);
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
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs) {
      Contract.Requires(lhs != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          Error(lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is FieldSelectExpr) {
        var ll = (FieldSelectExpr)lhs;
        if (!ll.Field.IsUserMutable) {
          Error(lhs, "LHS of assignment must denote a mutable field");
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        if (!UnifyTypes(ll.Seq.Type, builtIns.ArrayType(1, new InferredTypeProxy()))) {
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
        CheckForallStatementBodyRestrictions(s.Body, kind);

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
        CheckHintRestrictions(s.Body);

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
          Contract.Assert(rr.Arguments == null && rr.OptionalNameComponent == null && rr.InitCall == null);
          ResolveType(stmt.Tok, rr.EType, ResolveTypeOption.InferTypeProxies, null);
          int i = 0;
          if (rr.EType.IsSubrangeType) {
            Error(stmt, "sorry, cannot instantiate 'array' type with a subrange type");
          }
          foreach (Expression dim in rr.ArrayDimensions) {
            Contract.Assert(dim != null);
            ResolveExpression(dim, true, codeContext);
            if (!UnifyTypes(dim.Type, Type.Int)) {
              Error(stmt, "new must use an integer expression for the array size (got {0} for index {1})", dim.Type, i);
            }
            i++;
          }
          rr.Type = builtIns.ArrayType(rr.ArrayDimensions.Count, rr.EType);
        } else {
          var initCallTok = rr.Tok;
          if (rr.OptionalNameComponent == null && rr.Arguments != null) {
            // Resolve rr.EType and do one of three things:
            // * If rr.EType denotes a type, then set rr.OptionalNameComponent to "_ctor", which sets up a call to the default constructor.
            // * If the all-but-last components of rr.EType denote a type, then do EType,OptionalNameComponent := allButLast(EType),last(EType)
            // * Otherwise, report an error
            var ret = ResolveTypeLenient(stmt.Tok, rr.EType, ResolveTypeOption.InferTypeProxies, null, true);
            if (ret != null) {
              // While rr.EType does not denote a type, no error has been reported yet and the all-but-last components of rr.EType may
              // denote a type, so shift the last component to OptionalNameComponent and retry with the suggested type.
              rr.OptionalNameComponent = ret.LastName;
              rr.EType = ret.ReplacementType;
              initCallTok = ret.LastToken;
              ResolveType(stmt.Tok, rr.EType, ResolveTypeOption.InferTypeProxies, null);
            } else {
              // Either rr.EType resolved correctly as a type or there was no way to drop a last component to make it into something that looked
              // like a type.  In either case, set OptionalNameComponent to "_ctor" and continue.
              rr.OptionalNameComponent = "_ctor";
            }
          } else {
            ResolveType(stmt.Tok, rr.EType, ResolveTypeOption.InferTypeProxies, null);
          }
          if (!rr.EType.IsRefType) {
            Error(stmt, "new can be applied only to reference types (got {0})", rr.EType);
          } else {
            bool callsConstructor = false;
            if (rr.Arguments != null) {
              // ---------- new C.Init(EE)
              Contract.Assert(rr.OptionalNameComponent != null);  // if it wasn't non-null from the beginning, the code above would have set it to a non-null value
              rr.InitCall = new CallStmt(initCallTok, stmt.EndTok, new List<Expression>(), rr.ReceiverArgumentForInitCall, rr.OptionalNameComponent, rr.Arguments);
              ResolveCallStmt(rr.InitCall, specContextOnly, codeContext, rr.EType);
              if (rr.InitCall.Method is Constructor) {
                callsConstructor = true;
              }
            } else {
              // ---------- new C
              Contract.Assert(rr.ArrayDimensions == null && rr.OptionalNameComponent == null && rr.InitCall == null);
            }
            if (!callsConstructor && rr.EType is UserDefinedType) {
              var udt = (UserDefinedType)rr.EType;
              var cl = (ClassDecl)udt.ResolvedClass;  // cast is guaranteed by the call to rr.EType.IsRefType above, together with the "rr.EType is UserDefinedType" test
              if (cl.HasConstructor) {
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
      receiverType = receiverType.Normalize();
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
            Error(tok, "{0} {1} does not have a default constructor", kind, ctype.Name);
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

      Error(tok, "type {0} does not have a member {1}", receiverType, memberName);
      return null;
    }

    /// <summary>
    /// Returns a resolved FieldSelectExpr.
    /// </summary>
    public static FieldSelectExpr NewFieldSelectExpr(IToken tok, Expression obj, Field field, Dictionary<TypeParameter, Type> typeSubstMap) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(field != null);
      Contract.Requires(obj.Type != null);  // "obj" is required to be resolved
      var e = new FieldSelectExpr(tok, obj, field.Name);
      e.Field = field;  // resolve here
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
    public static Type SubstType(Type type, Dictionary<TypeParameter/*!*/, Type/*!*/>/*!*/ subst) {
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
          return new MapType(dom, ran);
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
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedParam != null) {
          Contract.Assert(t.TypeArgs.Count == 0);
          Type s;
          if (subst.TryGetValue(t.ResolvedParam, out s)) {
            return cce.NonNull(s);
          } else {
            return type;
          }
        } else if (t.ResolvedClass != null) {
          List<Type> newArgs = null;  // allocate it lazily
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
            return new UserDefinedType(t.tok, t.Name, t.ResolvedClass, newArgs, t.Path);
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

      List<Type> args = new List<Type>();
      foreach (TypeParameter tp in cl.TypeArgs) {
        args.Add(new UserDefinedType(tok, tp.Name, tp));
      }
      return new UserDefinedType(tok, cl.Name, cl, args);
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

    /// <summary>
    /// "twoState" implies that "old" and "fresh" expressions are allowed.
    /// </summary>
    void ResolveExpression(Expression expr, bool twoState, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(codeContext != null);
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
        ResolveExpression(e.E, twoState, codeContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, twoState, codeContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is IdentifierSequence) {
        var e = (IdentifierSequence)expr;
        ResolveIdentifierSequence(e, twoState, codeContext, false);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        var errorCount = ErrorCount;
        ResolveExpression(e.E, twoState, codeContext);
        e.Type = e.E.Type;
        if (errorCount != ErrorCount) {
          // there were errors resolving the operand; take the quick way out and
          // just let the (already erronous) subexpression be what the negation expression
          // will resolve to
          e.ResolvedExpression = e.E;
        } else {
          Expression zero;
          if (e.E.Type is RealType) {
            // we know for sure that this is a real-unary-minus
            zero = new LiteralExpr(e.tok, Basetypes.BigDec.ZERO);
          } else {
            // it's may be an integer operand or it may be that we don't know yet; we'll treat
            // two cases the same way
            zero = new LiteralExpr(e.tok, 0);
          }
          var subtract = new BinaryExpr(e.tok, BinaryExpr.Opcode.Sub, zero, e.E);
          // Resolve the subtraction expression.  This look like it will resolve e.E once more,
          // but the recursive calls to the resolver is mindful about DAGs and will check if the
          // subexpression has already been resolved.
          ResolveExpression(subtract, twoState, codeContext);
          e.ResolvedExpression = subtract;
        }

      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr) {
          StaticReceiverExpr eStatic = (StaticReceiverExpr)e;
          this.ResolveType(eStatic.tok, eStatic.UnresolvedType, ResolveTypeOption.InferTypeProxies, null);
          eStatic.Type = eStatic.UnresolvedType;
        } else {
          if (e.Value == null) {
            e.Type = new ObjectTypeProxy();
          } else if (e.Value is BigInteger) {
            e.Type = Type.Int;
          } else if (e.Value is Basetypes.BigDec) {
            e.Type = Type.Real;
          } else if (e.Value is bool) {
            e.Type = Type.Bool;
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
        } else if (d is AmbiguousTopLevelDecl) {
          Error(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1}", dtv.DatatypeName, ((AmbiguousTopLevelDecl)d).ModuleNames());
        } else if (!(d is DatatypeDecl)) {
          Error(expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        } else {
          ResolveDatatypeValue(twoState, codeContext, dtv, (DatatypeDecl)d);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy();
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, twoState, codeContext);
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
          ResolveExpression(p.A, twoState, codeContext);
          Contract.Assert(p.A.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(domainType, p.A.Type)) {
            Error(p.A, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", p.A.Type, domainType);
          }
          ResolveExpression(p.B, twoState, codeContext);
          Contract.Assert(p.B.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(rangeType, p.B.Type)) {
            Error(p.B, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", p.B.Type, rangeType);
          }
        }
        expr.Type = new MapType(domainType, rangeType);
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        // The following call to ResolveExpression is just preliminary.  If it succeeds, it is redone below on the resolved expression.  Thus,
        // it's okay to be more lenient here and use coLevel (instead of trying to use CoLevel_Dec(coLevel), which is needed when .Name denotes a
        // destructor for a co-datatype).
        ResolveExpression(e.Obj, twoState, codeContext);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        Expression resolved = ResolvePredicateOrField(expr.tok, e.Obj, e.SuffixName);
        if (resolved == null) {
          // error has already been reported by ResolvePredicateOrField
        } else {
          // the following will cause e.Obj to be resolved again, but that's still correct
          e.ResolvedExpression = resolved;
          ResolveExpression(e.ResolvedExpression, twoState, codeContext);
          e.Type = e.ResolvedExpression.Type;
        }

      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        ResolveExpression(e.Obj, twoState, codeContext);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        NonProxyType nptype;
        MemberDecl member = ResolveMember(expr.tok, e.Obj.Type, e.FieldName, out nptype);
#if !NO_WORK_TO_BE_DONE
        UserDefinedType ctype = (UserDefinedType)nptype;
#endif
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          Error(expr, "member {0} in type {1} does not refer to a field", e.FieldName, cce.NonNull(ctype).Name);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          e.Field = (Field)member;
          if (e.Obj is StaticReceiverExpr) {
            Error(expr, "a field must be selected via an object, not just a class name");
          }
          // build the type substitution map
          var subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
          e.Type = SubstType(e.Field.Type, subst);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, twoState, codeContext, true);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, twoState, codeContext);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        if (!UnifyTypes(e.Array.Type, builtIns.ArrayType(e.Indices.Count, elementType))) {
          Error(e.Array, "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        }
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, twoState, codeContext);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(idx.Type, Type.Int)) {
            Error(idx, "array selection requires integer indices (got {0} for index {1})", idx.Type, i);
          }
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, twoState, codeContext);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        if (UnifyTypes(e.Seq.Type, new SeqType(elementType))) {
          ResolveExpression(e.Index, twoState, codeContext);
          Contract.Assert(e.Index.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Index.Type, Type.Int)) {
            Error(e.Index, "sequence update requires integer index (got {0})", e.Index.Type);
          }
          ResolveExpression(e.Value, twoState, codeContext);
          Contract.Assert(e.Value.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Value.Type, elementType)) {
            Error(e.Value, "sequence update requires the value to have the element type of the sequence (got {0})", e.Value.Type);
          }
          expr.Type = e.Seq.Type;
        } else if (UnifyTypes(e.Seq.Type, new MapType(domainType, rangeType))) {
          ResolveExpression(e.Index, twoState, codeContext);
          if (!UnifyTypes(e.Index.Type, domainType)) {
            Error(e.Index, "map update requires domain element to be of type {0} (got {1})", domainType, e.Index.Type);
          }
          ResolveExpression(e.Value, twoState, codeContext);
          if (!UnifyTypes(e.Value.Type, rangeType)) {
            Error(e.Value, "map update requires the value to have the range type {0} (got {1})", rangeType, e.Value.Type);
          }
          expr.Type = e.Seq.Type;
        } else if (UnifyTypes(e.Seq.Type, new MultiSetType(elementType))) {
          ResolveExpression(e.Index, twoState, codeContext);
          if (!UnifyTypes(e.Index.Type, elementType)) {
            Error(e.Index, "multiset update requires domain element to be of type {0} (got {1})", elementType, e.Index.Type);
          }
          ResolveExpression(e.Value, twoState, codeContext);
          if (!UnifyTypes(e.Value.Type, Type.Int)) {
            Error(e.Value, "multiset update requires integer value (got {0})", e.Value.Type);
          }
          expr.Type = e.Seq.Type;

        }
        else if (e.Seq.Type is UserDefinedType && ((UserDefinedType)e.Seq.Type).IsDatatype)
        {
          DatatypeDecl dt = ((UserDefinedType)e.Seq.Type).AsDatatype;

          if (!(e.Index is IdentifierSequence || (e.Index is LiteralExpr && ((LiteralExpr)e.Index).Value is BigInteger)))
          {
            Error(expr, "datatype updates must be to datatype destructors");
          } else {
            string destructor_str = null;

            if (e.Index is IdentifierSequence)
            {
              IdentifierSequence iseq = (IdentifierSequence)e.Index;

              if (iseq.Tokens.Count() != 1)
              {
                Error(expr, "datatype updates must name a single datatype destructor");
              }
              else
              {
                destructor_str = iseq.Tokens.First().val;
              }
            }
            else
            {
              Contract.Assert(e.Index is LiteralExpr && ((LiteralExpr)e.Index).Value is BigInteger);
              destructor_str = ((LiteralExpr)e.Index).tok.val;
            }

            if (destructor_str != null)
            {
              MemberDecl member;
              if (!datatypeMembers[dt].TryGetValue(destructor_str, out member))
              {
                Error(expr, "member {0} does not exist in datatype {1}", destructor_str, dt.Name);
              }
              else
              {
                // Rewrite an update of the form "dt[dtor := E]" to be "dtCtr(E, dt.dtor2, dt.dtor3,...)"
                DatatypeDestructor destructor = (DatatypeDestructor)member;
                DatatypeCtor ctor = destructor.EnclosingCtor;

                List<Expression> ctor_args = new List<Expression>();
                foreach (Formal d in ctor.Formals)
                {
                  if (d.Name == destructor.Name)
                  {
                    ctor_args.Add(e.Value);
                  }
                  else
                  {
                    ctor_args.Add(new ExprDotName(expr.tok, e.Seq, d.Name));
                  }
                }

                DatatypeValue ctor_call = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, ctor.Name, ctor_args);
                ResolveExpression(ctor_call, twoState, codeContext);
                e.ResolvedUpdateExpr = ctor_call;

                expr.Type = e.Seq.Type;
              }
            }
          }
        }
        else
        {
          Error(expr, "update requires a sequence, map, or datatype (got {0})", e.Seq.Type);
        }


      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, twoState, codeContext, false);

      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        if (!twoState) {
          Error(expr, "old expressions are not allowed in this context");
        }
        ResolveExpression(e.E, twoState, codeContext);
        expr.Type = e.E.Type;

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, twoState, codeContext);
        if (!UnifyTypes(e.E.Type, new SetType(new InferredTypeProxy())) && !UnifyTypes(e.E.Type, new SeqType(new InferredTypeProxy()))) {
          Error(e.tok, "can only form a multiset from a seq or set.");
        }
        expr.Type = new MultiSetType(((CollectionType)e.E.Type).Arg);
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        if (!twoState) {
          Error(expr, "fresh expressions are not allowed in this context");
        }
        ResolveExpression(e.E, twoState, codeContext);
        // the type of e.E must be either an object or a collection of objects
        Type t = e.E.Type;
        Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
        if (t is CollectionType) {
          t = ((CollectionType)t).Arg;
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

      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        ResolveExpression(e.E, twoState, codeContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case UnaryExpr.Opcode.Not:
            if (!UnifyTypes(e.E.Type, Type.Bool)) {
              Error(expr, "logical negation expects a boolean argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Bool;
            break;
          case UnaryExpr.Opcode.SeqLength:
            if (!UnifyTypes(e.E.Type, new CollectionTypeProxy(new InferredTypeProxy()))) {
              Error(expr, "size operator expects a collection argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Int;
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, twoState, codeContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, twoState, codeContext);
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
                !UnifyTypes(e.E0.Type, new MapType(new InferredTypeProxy(), new InferredTypeProxy()))) {
              Error(expr, "arguments must be of a [multi]set or map type (got {0})", e.E0.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le:
          case BinaryExpr.Opcode.Add: {
              if (e.Op == BinaryExpr.Opcode.Lt && e.E0.Type.IsIndDatatype) {
                if (UnifyTypes(e.E1.Type, new DatatypeProxy(false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                expr.Type = Type.Bool;
              } else if (e.Op == BinaryExpr.Opcode.Lt && e.E1.Type.IsIndDatatype) {
                if (UnifyTypes(e.E0.Type, new DatatypeProxy(false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E0.Type);
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true))) {
                  Error(expr, "arguments to {0} must be int or real or a collection type (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
                  err = true;
                }
                if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
                  Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
                  err = true;
                }
                if (e.Op != BinaryExpr.Opcode.Add) {
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
              if (e.Op == BinaryExpr.Opcode.Gt && e.E0.Type.IsIndDatatype) {
                if (UnifyTypes(e.E1.Type, new DatatypeProxy(false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                expr.Type = Type.Bool;
              } else if (e.Op == BinaryExpr.Opcode.Gt && e.E1.Type.IsIndDatatype) {
                if (UnifyTypes(e.E0.Type, new DatatypeProxy(false))) {
                  e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
                } else {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E0.Type);
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(false))) {
                  Error(expr, "arguments to {0} must be int or real or a set (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
                  err = true;
                }
                if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
                  Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
                  err = true;
                }
                if (e.Op == BinaryExpr.Opcode.Gt || e.Op == BinaryExpr.Opcode.Ge) {
                  expr.Type = Type.Bool;
                } else if (!err) {
                  expr.Type = e.E0.Type;
                }
              }
            }
            break;

          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            if (!UnifyTypes(e.E1.Type, new CollectionTypeProxy(e.E0.Type))) {
              Error(expr, "second argument to \"{0}\" must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Div:
            if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(false))) {
              // TODO: this should disallow OperationTypeProxy types except for int and real
              Error(expr, "first argument to {0} must be of type int or real (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, e.E0.Type)) {
              Error(expr, "arguments to {0} must have the same type (got {1} and {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
            }
            expr.Type = e.E0.Type;
            break;

          case BinaryExpr.Opcode.Mod:
            if (!UnifyTypes(e.E0.Type, Type.Int)) {
              Error(expr, "first argument to {0} must be of type int (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
            }
            if (!UnifyTypes(e.E1.Type, Type.Int)) {
              Error(expr, "second argument to {0} must be of type int (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
            }
            expr.Type = Type.Int;
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
        }
        // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
        // setting e.ResolvedOp until inside CheckTypeInference.

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, twoState, codeContext);
        ResolveExpression(e.E1, twoState, codeContext);
        ResolveExpression(e.E2, twoState, codeContext);
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
            ResolveExpression(rhs, twoState, codeContext);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            Error(expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            var c = 0;
            foreach (var v in lhs.Vars) {
              if (!scope.Push(v.Name, v)) {
                Error(v, "Duplicate let-variable name: {0}", v.Name);
              }
              c++;
            }
            if (c == 0) {
              // Every identifier-looking thing in the patterned resolved to a constructor; that is, this LHS is a constant literal
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
            ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, twoState, codeContext);
            if (!UnifyTypes(rhs.Type, Type.Bool)) {
              Error(rhs.tok, "type of RHS of let-such-that expression must be boolean (got {0})", rhs.Type);
            }
          }
        }
        ResolveExpression(e.Body, twoState, codeContext);
        scope.PopMarker();
        expr.Type = e.Body.Type;

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        ResolveExpression(e.Body, twoState, codeContext);
        if (e.Contract != null) ResolveExpression(e.Contract, twoState, codeContext);
        e.Type = e.Body.Type;
      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, twoState, codeContext);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(e.Range.Type, Type.Bool)) {
            Error(expr, "range of quantifier must be of type bool (instead got {0})", e.Range.Type);
          }
        }
        ResolveExpression(e.Term, twoState, codeContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Term.Type, Type.Bool)) {
          Error(expr, "body of quantifier must be of type bool (instead got {0})", e.Term.Type);
        }
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e.Attributes, twoState, codeContext);
        scope.PopMarker();
        expr.Type = Type.Bool;

        if (prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.LogicalBody());  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.LogicalBody(), e is ExistsExpr, false, missingBounds);
          if (missingBounds.Count != 0) {
            // Report errors here about quantifications that depend on the allocation state.
            var mb = missingBounds;
            if (codeContext is Function) {
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
          ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
        }
        ResolveExpression(e.Range, twoState, codeContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Range.Type, Type.Bool)) {
          Error(expr, "range of comprehension must be of type bool (instead got {0})", e.Range.Type);
        }
        ResolveExpression(e.Term, twoState, codeContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, twoState, codeContext);
        scope.PopMarker();
        expr.Type = new SetType(e.Term.Type);

        if (prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.Range);  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            e.MissingBounds = missingBounds;
            foreach (var bv in e.MissingBounds) {
              Error(expr, "a set comprehension must produce a finite set, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
            }
          }
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
          ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
        }
        ResolveExpression(e.Range, twoState, codeContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Range.Type, Type.Bool)) {
          Error(expr, "range of comprehension must be of type bool (instead got {0})", e.Range.Type);
        }
        ResolveExpression(e.Term, twoState, codeContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, twoState, codeContext);
        scope.PopMarker();
        expr.Type = new MapType(e.BoundVars[0].Type, e.Term.Type);

        if (prevErrorCount == ErrorCount) {
          var missingBounds = new List<BoundVar>();
          CheckTypeInference(e.Range);  // we need to resolve operators before the call to DiscoverBounds
          e.Bounds = DiscoverBounds(e.tok, e.BoundVars, e.Range, true, false, missingBounds);
          if (missingBounds.Count != 0) {
            e.MissingBounds = missingBounds;
            foreach (var bv in e.MissingBounds) {
              Error(expr, "a map comprehension must produce a finite domain, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
            }
          }
        }

      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(new ObjectType());

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = ErrorCount;
        ResolveStatement(e.S, true, codeContext);
        if (ErrorCount == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method.Mod.Expressions.Count != 0) {
              Error(call, "calls to methods with side-effects are not allowed inside a statement expression");
            }
          }
        }
        ResolveExpression(e.E, twoState, codeContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, twoState, codeContext);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, twoState, codeContext);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, twoState, codeContext);
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
        ResolveExpression(me.Source, twoState, codeContext);
        Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        Dictionary<TypeParameter, Type> subst = new Dictionary<TypeParameter, Type>();
        if (me.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)me.Source.Type;
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
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
            ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
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
          ResolveExpression(mc.Body, twoState, codeContext);
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
        expr.Type = Type.Flexible;
      }
    }

    void ResolveCasePattern(CasePattern pat, Type sourceType) {
      Contract.Requires(pat != null);
      Contract.Requires(sourceType != null);

      DatatypeDecl dtd = null;
      UserDefinedType udt = null;
      if (sourceType.IsDatatype) {
        udt = (UserDefinedType)sourceType;
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
        ResolveType(v.tok, v.Type, ResolveTypeOption.InferTypeProxies, null);
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
            ResolveCasePattern(arg, st);
          }
          j++;
        }
        if (j == ctor.Formals.Count) {
          pat.AssembleExpr(udt.TypeArgs);
        }
      }
    }

    private void ResolveDatatypeValue(bool twoState, ICodeContext codeContext, DatatypeValue dtv, DatatypeDecl dt) {
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
      dtv.Type = new UserDefinedType(dtv.tok, dtv.DatatypeName, dt, gt);

      DatatypeCtor ctor;
      if (!datatypeCtors[dt].TryGetValue(dtv.MemberName, out ctor)) {
        Error(dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
      } else {
        Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
        if (ctor.Formals.Count != dtv.Arguments.Count) {
          Error(dtv.tok, "wrong number of arguments to datatype constructor {0} (found {1}, expected {2})", dtv.DatatypeName, dtv.Arguments.Count, ctor.Formals.Count);
        }
      }
      int j = 0;
      foreach (Expression arg in dtv.Arguments) {
        Formal formal = ctor != null && j < ctor.Formals.Count ? ctor.Formals[j] : null;
        ResolveExpression(arg, twoState, codeContext);
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
      if (A.IsArrayType && B.IsArrayType) {
        Type a = UserDefinedType.ArrayElementType(A);
        Type b = UserDefinedType.ArrayElementType(B);
        return CouldPossiblyBeSameType(a, b);
      } else
        if (A is UserDefinedType && B is UserDefinedType) {
          UserDefinedType a = (UserDefinedType)A;
          UserDefinedType b = (UserDefinedType)B;
          if (a.ResolvedClass != null && b.ResolvedClass != null && a.ResolvedClass.Name == b.ResolvedClass.Name) {
            if (a.TypeArgs.Count != b.TypeArgs.Count) {
              return false; // this probably doesn't happen if the classes are the same.
            }
            for (int i = 0; i < a.TypeArgs.Count; i++) {
              if (!CouldPossiblyBeSameType(a.TypeArgs[i], b.TypeArgs[i]))
                return false;
            }
            // all parameters could be the same
            return true;
          }
          // either we don't know what class it is yet, or the classes mismatch
          return false;
        }
      return false;
    }
    private bool CouldPossiblyBeSameType(Type A, Type B) {
      if (A.IsTypeParameter || B.IsTypeParameter) {
        return true;
      }
      if (A.IsArrayType && B.IsArrayType) {
        Type a = UserDefinedType.ArrayElementType(A);
        Type b = UserDefinedType.ArrayElementType(B);
        return CouldPossiblyBeSameType(a, b);
      }
      if (A is UserDefinedType && B is UserDefinedType) {
        UserDefinedType a = (UserDefinedType)A;
        UserDefinedType b = (UserDefinedType)B;
        if (a.ResolvedClass != null && b.ResolvedClass != null && a.ResolvedClass == b.ResolvedClass) {
          if (a.TypeArgs.Count != b.TypeArgs.Count) {
            return false; // this probably doesn't happen if the classes are the same.
          }
          for (int i = 0; i < a.TypeArgs.Count; i++) {
            if (!CouldPossiblyBeSameType(a.TypeArgs[i], b.TypeArgs[i]))
              return false;
          }
          // all parameters could be the same
          return true;
        }
        // either we don't know what class it is yet, or the classes mismatch
        return false;
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

      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        if (e.Field != null && e.Field.IsGhost) {
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

      } else if (expr is FreshExpr) {
        Error(expr, "fresh expressions are allowed only in specification and ghost contexts");
        return;

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
        if (!e.Exact) {
          Error(expr, "let-such-that expressions are allowed only in ghost contexts");
        }
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);
        var i = 0;
        foreach (var ee in e.RHSs) {
          if (!e.LHSs[i].Vars.All(bv => bv.IsGhost)) {
            CheckIsNonGhost(ee);
          }
          i++;
        }
        CheckIsNonGhost(e.Body);
        return;
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (e.MissingBounds != null) {
          foreach (var bv in e.MissingBounds) {
            Error(expr, "quantifiers in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{0}'", bv.Name);
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
      }

      foreach (var ee in expr.SubExpressions) {
        CheckIsNonGhost(ee);
      }
    }

    /// <summary>
    /// If "!allowMethodCall" or if what is being called does not refer to a method, resolves "e" and returns "null".
    /// Otherwise (that is, if "allowMethodCall" and what is being called refers to a method), resolves the receiver
    /// of "e" but NOT the arguments, and returns a CallRhs corresponding to the call.
    /// </summary>
    CallRhs ResolveFunctionCallExpr(FunctionCallExpr e, bool twoState, ICodeContext codeContext, bool allowMethodCall) {
      ResolveReceiver(e.Receiver, twoState, codeContext);
      Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression
      NonProxyType nptype;
      MemberDecl member = ResolveMember(e.tok, e.Receiver.Type, e.Name, out nptype);
#if !NO_WORK_TO_BE_DONE
      UserDefinedType ctype = (UserDefinedType)nptype;
#endif
      if (member == null) {
        // error has already been reported by ResolveMember
      } else if (member is Method) {
        if (allowMethodCall) {
          // it's a method
          return new CallRhs(e.tok, e.Receiver, e.Name, e.Args);
        } else {
          Error(e, "member {0} in type {1} refers to a method, but only functions can be used in this context", e.Name, cce.NonNull(ctype).Name);
        }
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
            ResolveExpression(farg, twoState, codeContext);
            Contract.Assert(farg.Type != null);  // follows from postcondition of ResolveExpression
            Type s = SubstType(function.Formals[i].Type, e.TypeArgumentSubstitutions);
            if (!UnifyTypes(farg.Type, s)) {
              Error(e, "incorrect type of function argument {0} (expected {1}, got {2})", i, s, farg.Type);
            }
          }
          e.Type = SubstType(function.ResultType, e.TypeArgumentSubstitutions);
        }

        // Resolution termination check
        ModuleDefinition callerModule = codeContext.EnclosingModule;
        ModuleDefinition calleeModule = function.EnclosingClass.Module;
        if (callerModule == calleeModule) {
          // intra-module call; add edge in module's call graph
          var caller = codeContext as ICallable;
          if (caller == null) {
            // don't add anything to the call graph after all
          } else if (caller is IteratorDecl) {
            callerModule.CallGraph.AddEdge(((IteratorDecl)codeContext).Member_MoveNext, function);
          } else {
            callerModule.CallGraph.AddEdge(caller, function);
            if (caller is Function) {
              ((Function)caller).AllCalls.Add(e);
            }
            if (caller == function) {
              function.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
            }
          }
        }
      }
      return null;
    }

    /// <summary>
    /// If "!allowMethodCall", or if "e" does not designate a method call, resolves "e" and returns "null".
    /// Otherwise, resolves all sub-parts of "e" and returns a (resolved) CallRhs expression representing the call.
    /// </summary>
    CallRhs ResolveIdentifierSequence(IdentifierSequence e, bool twoState, ICodeContext codeContext, bool allowMethodCall) {
      // Look up "id" as follows:
      //  - local variable, parameter, or bound variable (if this clashes with something of interest, one can always rename the local variable locally)
      //  - unamibugous type/module name (class, datatype, sub-module (including submodules of imports) or arbitrary-type)
      //       (if two imported types have the same name, an error message is produced here)
      //  - unambiguous constructor name of a datatype (if two constructors have the same name, an error message is produced here)
      //  - field, function or method name (with implicit receiver) (if the field is occluded by anything above, one can use an explicit "this.")
      //  - iterator
      //  - static function or method in the enclosing module, or its imports.

      Expression r = null;  // resolved version of e
      CallRhs call = null;

      TopLevelDecl decl;
      Tuple<DatatypeCtor, bool> pair;
      Dictionary<string, MemberDecl> members;
      MemberDecl member;
      var id = e.Tokens[0];
      if (scope.Find(id.val) != null) {
        // ----- root is a local variable, parameter, or bound variable
        r = new IdentifierExpr(id, id.val);
        ResolveExpression(r, twoState, codeContext);
        r = ResolveSuffix(r, e, 1, twoState, codeContext,  allowMethodCall, out call);

      } else if (moduleInfo.TopLevels.TryGetValue(id.val, out decl)) {
        if (decl is AmbiguousTopLevelDecl) {
          Error(id, "The name {0} ambiguously refers to a type in one of the modules {1}", id.val, ((AmbiguousTopLevelDecl)decl).ModuleNames());
        } else if (e.Tokens.Count == 1 && e.Arguments == null) {
          Error(id, "name of type ('{0}') is used as a variable", id.val);
        } else if (e.Tokens.Count == 1 && e.Arguments != null) {
          Error(id, "name of type ('{0}') is used as a function", id.val);
          // resolve the arguments nonetheless
          foreach (var arg in e.Arguments) {
            ResolveExpression(arg, twoState, codeContext);
          }
        } else if (decl is ClassDecl) {
          // ----- root is a class
          var cd = (ClassDecl)decl;
          r = ResolveSuffix(new StaticReceiverExpr(id, cd), e, 1, twoState, codeContext, allowMethodCall, out call);

        } else if (decl is ModuleDecl) {
          // ----- root is a submodule
          if (!(1 < e.Tokens.Count)) {
            Error(e.tok, "module {0} cannot be used here", ((ModuleDecl)decl).Name);
          }
          call = ResolveIdentifierSequenceModuleScope(e, 1, ((ModuleDecl)decl).Signature, twoState, codeContext, allowMethodCall);
        } else {
          // ----- root is a datatype
          var dt = (DatatypeDecl)decl;  // otherwise, unexpected TopLevelDecl
          var args = (e.Tokens.Count == 2 ? e.Arguments : null) ?? new List<Expression>();
          r = new DatatypeValue(id, id.val, e.Tokens[1].val, args);
          ResolveExpression(r, twoState, codeContext);
          if (e.Tokens.Count != 2) {
            r = ResolveSuffix(r, e, 2, twoState, codeContext, allowMethodCall, out call);
          }
        }

      } else if (moduleInfo.Ctors.TryGetValue(id.val, out pair)) {
        // ----- root is a datatype constructor
        if (pair.Item2) {
          // there is more than one constructor with this name
          Error(id, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", id.val, pair.Item1.EnclosingDatatype.Name);
        } else {
          var args = (e.Tokens.Count == 1 ? e.Arguments : null) ?? new List<Expression>();
          r = new DatatypeValue(id, pair.Item1.EnclosingDatatype.Name, id.val, args);
          ResolveExpression(r, twoState, codeContext);
          if (e.Tokens.Count != 1) {
            r = ResolveSuffix(r, e, 1, twoState, codeContext, allowMethodCall, out call);
          }
        }

      } else if ((currentClass != null && classMembers.TryGetValue(currentClass, out members) && members.TryGetValue(id.val, out member))
                 || moduleInfo.StaticMembers.TryGetValue(id.val, out member)) // try static members of the current module too.
      {
        // ----- field, function, or method
        if (member is AmbiguousMemberDecl) {
          Contract.Assert(member.IsStatic); // currently, static members of _default are the only thing which can be ambiguous.
          Error(id, "The name {0} ambiguously refers to a static member in one of the modules {1}", id.val, ((AmbiguousMemberDecl)member).ModuleNames());
        } else {
          Expression receiver;
          if (member.IsStatic) {
            receiver = new StaticReceiverExpr(id, (ClassDecl)member.EnclosingClass);
          } else {
            if (!scope.AllowInstance) {
              Error(id, "'this' is not allowed in a 'static' context");
              // nevertheless, set "receiver" to a value so we can continue resolution
            }
            receiver = new ImplicitThisExpr(id);
            receiver.Type = GetThisType(id, (ClassDecl)member.EnclosingClass);  // resolve here
          }
          r = ResolveSuffix(receiver, e, 0, twoState, codeContext, allowMethodCall, out call);
        }

      } else {
        Error(id, "unresolved identifier: {0}", id.val);
        // resolve arguments, if any
        if (e.Arguments != null) {
          foreach (var arg in e.Arguments) {
            ResolveExpression(arg, twoState, codeContext);
          }
        }
      }

      if (r != null) {
        e.ResolvedExpression = r;
        e.Type = r.Type;
      }
      return call;
    }

    CallRhs ResolveIdentifierSequenceModuleScope(IdentifierSequence e, int p, ModuleSignature sig, bool twoState, ICodeContext codeContext, bool allowMethodCall) {
      // Look up "id" as follows:
      //  - unamibugous type/module name (class, datatype, sub-module (including submodules of imports) or arbitrary-type)
      //       (if two imported types have the same name, an error message is produced here)
      //  - static function or method of sig.
      // This is used to look up names that appear after a dot in a sequence identifier. For example, in X.M.*, M should be looked up in X, but
      // should not consult the local scope. This distingushes this from the above, in that local scope, imported modules, etc. are ignored.
      Contract.Requires(0 <= p && p < e.Tokens.Count);
      Expression r = null;  // resolved version of e
      CallRhs call = null;

      TopLevelDecl decl;
      MemberDecl member;
      Tuple<DatatypeCtor, bool> pair;
      var id = e.Tokens[p];
      sig = GetSignature(sig);
      if (sig.TopLevels.TryGetValue(id.val, out decl)) {
        if (decl is AmbiguousTopLevelDecl) {
          Error(id, "The name {0} ambiguously refers to a something in one of the modules {1}", id.val, ((AmbiguousTopLevelDecl)decl).ModuleNames());
        } else if (decl is ClassDecl) {
          // ----- root is a class
          var cd = (ClassDecl)decl;
          r = ResolveSuffix(new StaticReceiverExpr(id, cd), e, p + 1, twoState, codeContext, allowMethodCall, out call);

        } else if (decl is ModuleDecl) {
          // ----- root is a submodule
          if (!(p + 1 < e.Tokens.Count)) {
            Error(e.tok, "module {0} cannot be used here", ((ModuleDecl)decl).Name);
          }
          call = ResolveIdentifierSequenceModuleScope(e, p + 1, ((ModuleDecl)decl).Signature, twoState, codeContext, allowMethodCall);
        } else {
          // ----- root is a datatype
          var dt = (DatatypeDecl)decl;  // otherwise, unexpected TopLevelDecl
          var args = (e.Tokens.Count == p + 2 ? e.Arguments : null) ?? new List<Expression>();
          r = new DatatypeValue(id, id.val, e.Tokens[p + 1].val, args);
          ResolveDatatypeValue(twoState, codeContext, (DatatypeValue)r, dt);
          if (e.Tokens.Count != p + 2) {
            r = ResolveSuffix(r, e, p + 2, twoState, codeContext, allowMethodCall, out call);
          }
        }
      } else if (sig.Ctors.TryGetValue(id.val, out pair)) {
        // ----- root is a datatype constructor
        if (pair.Item2) {
          // there is more than one constructor with this name
          Error(id, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", id.val, pair.Item1.EnclosingDatatype.Name);
        } else {
          var dt = pair.Item1.EnclosingDatatype;
          var args = (e.Tokens.Count == p + 1 ? e.Arguments : null) ?? new List<Expression>();
          r = new DatatypeValue(id, dt.Name, id.val, args);
          ResolveDatatypeValue(twoState, codeContext, (DatatypeValue)r, dt);
          if (e.Tokens.Count != p + 1) {
            r = ResolveSuffix(r, e, p + 1, twoState, codeContext, allowMethodCall, out call);
          }
        }
      } else if (sig.StaticMembers.TryGetValue(id.val, out member)) // try static members of the current module too.
      {
        // ----- function, or method
        Expression receiver;
        Contract.Assert(member.IsStatic);
        receiver = new StaticReceiverExpr(id, (ClassDecl)member.EnclosingClass);
        r = ResolveSuffix(receiver, e, p, twoState, codeContext, allowMethodCall, out call);

      } else {
        Error(id, "unresolved identifier: {0}", id.val);
        // resolve arguments, if any
        if (e.Arguments != null) {
          foreach (var arg in e.Arguments) {
            ResolveExpression(arg, twoState, codeContext);
          }
        }
      }

      if (r != null) {
        e.ResolvedExpression = r;
        e.Type = r.Type;
      }
      return call;
    }

    private ModuleSignature GetSignature(ModuleSignature sig) {
      if (useCompileSignatures) {
        while (sig.CompileSignature != null)
          sig = sig.CompileSignature;
      }
      return sig;
    }
    /// <summary>
    /// Given resolved expression "r" and unresolved expressions e.Tokens[p..] and e.Arguments.
    /// Returns a resolved version of the expression:
    ///   r    . e.Tokens[p]    . e.Tokens[p+1]    ...    . e.Tokens[e.Tokens.Count-1]    ( e.Arguments )
    /// Except, if "allowMethodCall" is "true" and the would-be-returned value designates a method
    /// call, instead returns null and returns "call" as a non-null value.
    /// </summary>
    Expression ResolveSuffix(Expression r, IdentifierSequence e, int p, bool twoState, ICodeContext codeContext, bool allowMethodCall, out CallRhs call) {
      Contract.Requires(r != null);
      Contract.Requires(e != null);
      Contract.Requires(0 <= p && p <= e.Tokens.Count);
      Contract.Ensures((Contract.Result<Expression>() != null && Contract.ValueAtReturn(out call) == null) ||
        (allowMethodCall && Contract.Result<Expression>() == null && Contract.ValueAtReturn(out call) != null));

      call = null;
      int nonCallArguments = e.Arguments == null ? e.Tokens.Count : e.Tokens.Count - 1;
      for (; p < nonCallArguments; p++) {
        var resolved = ResolvePredicateOrField(e.Tokens[p], r, e.Tokens[p].val);
        if (resolved != null) {
          r = resolved;
          ResolveExpression(r, twoState, codeContext);
        }
      }

      if (p < e.Tokens.Count) {
        Contract.Assert(e.Arguments != null);

        bool itIsAMethod = false;
        if (allowMethodCall) {
          var udt = r.Type.Normalize() as UserDefinedType;
          if (udt != null && udt.ResolvedClass != null) {
            Dictionary<string, MemberDecl> members;
            if (udt.ResolvedClass is ClassDecl) {
              classMembers.TryGetValue((ClassDecl)udt.ResolvedClass, out members);
            } else {
              members = null;
            }
            MemberDecl member;
            if (members != null && members.TryGetValue(e.Tokens[p].val, out member) && member is Method) {
              itIsAMethod = true;
            }
          }
        }
        if (itIsAMethod) {
          // method
          call = new CallRhs(e.Tokens[p], r, e.Tokens[p].val, e.Arguments);
          r = null;
        } else {
          r = new FunctionCallExpr(e.Tokens[p], e.Tokens[p].val, r, e.OpenParen, e.Arguments);
          ResolveExpression(r, twoState, codeContext);
        }
      } else if (e.Arguments != null) {
        Contract.Assert(p == e.Tokens.Count);
        Error(e.OpenParen, "non-function expression is called with parameters");
        // resolve the arguments nonetheless
        foreach (var arg in e.Arguments) {
          ResolveExpression(arg, twoState, codeContext);
        }
      }
      return r;
    }

    /// <summary>
    /// Resolves "obj . suffixName" to either a parameter-less predicate invocation or a field selection.
    /// Expects "obj" already to have been resolved.
    /// On success, returns the result of the resolution--as an un-resolved expression.
    /// On failure, returns null (in which case an error has been reported to the user).
    /// </summary>
    Expression/*?*/ ResolvePredicateOrField(IToken tok, Expression obj, string suffixName) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(obj.Type != null);  // obj is expected already to have been resolved
      Contract.Requires(suffixName != null);

      NonProxyType nptype;
      MemberDecl member = ResolveMember(tok, obj.Type, suffixName, out nptype);
      if (member == null) {
        // error has already been reported by ResolveMember
        return null;
      } else if (member is Predicate && ((Predicate)member).Formals.Count == 0) {
        // parameter-less predicates are allowed to be used without parentheses
        return new FunctionCallExpr(tok, suffixName, obj, null, new List<Expression>());
      } else {
        // assume it's a field and let the resolution of the FieldSelectExpr check any further problems
        return new FieldSelectExpr(tok, obj, suffixName);
      }
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
      for (int j = 0; j < bvars.Count; j++) {
        var bv = bvars[j];
        var bounds = new List<ComprehensionExpr.BoundedPool>();
        if (bv.Type is BoolType) {
          // easy
          bounds.Add(new ComprehensionExpr.BoolBoundedPool());
        } else {
          bool foundBoundsForBv = false;
          if (bv.Type.IsIndDatatype && (bv.Type.AsIndDatatype).HasFinitePossibleValues) {
            bounds.Add(new ComprehensionExpr.DatatypeBoundedPool(bv.Type.AsIndDatatype));
            foundBoundsForBv = true;
          }
          // Go through the conjuncts of the range expression to look for bounds.
          Expression lowerBound = bv.Type is NatType ? Expression.CreateIntLiteral(bv.Tok, 0) : null;
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
                if (whereIsBv == 0) {
                  bounds.Add(new ComprehensionExpr.SetBoundedPool(e1));
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
                if (whereIsBv == 0 && upperBound == null) {
                  upperBound = e1;  // bv < E
                } else if (whereIsBv == 1 && lowerBound == null) {
                  lowerBound = Expression.CreateIncrement(e0, 1);  // E < bv
                }
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                if (whereIsBv == 0 && upperBound == null) {
                  upperBound = Expression.CreateIncrement(e1, 1);  // bv <= E
                } else if (whereIsBv == 1 && lowerBound == null) {
                  lowerBound = e0;  // E <= bv
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
      var u = expr as UnaryExpr;
      if (u != null && u.Op == UnaryExpr.Opcode.Not) {
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
        expr = new UnaryExpr(expr.tok, UnaryExpr.Opcode.Not, expr);
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

    void ResolveReceiver(Expression expr, bool twoState, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is ThisExpr && !expr.WasResolved()) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        Contract.Assume(currentClass != null);  // this is really a precondition, in this case
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, twoState, codeContext);
      }
    }

    void ResolveSeqSelectExpr(SeqSelectExpr e, bool twoState, ICodeContext codeContext, bool allowNonUnitArraySelection) {
      Contract.Requires(e != null);
      if (e.Type != null) {
        // already resolved
        return;
      }

      bool seqErr = false;
      ResolveExpression(e.Seq, twoState, codeContext);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
      Type elementType = new InferredTypeProxy();
      Type domainType = new InferredTypeProxy();
      Type argType = new InferredTypeProxy();

      IndexableTypeProxy expectedType = new IndexableTypeProxy(domainType, elementType, argType, true);
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
          if (UnifyTypes(expectedType, new MapType(new InferredTypeProxy(), new InferredTypeProxy()))) {
            Error(e, "cannot multiselect a map (got {0} as map type)", e.Seq.Type);
          }
        }
      }
      if (e.E0 != null) {
        ResolveExpression(e.E0, twoState, codeContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E0.Type, domainType)) {
          Error(e.E0, "sequence/array/multiset/map selection requires {1} indices (got {0})", e.E0.Type, domainType);
        }
      }
      if (e.E1 != null) {
        ResolveExpression(e.E1, twoState, codeContext);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E1.Type, domainType)) {
          Error(e.E1, "sequence/array/multiset/map selection requires {1} indices (got {0})", e.E1.Type, domainType);
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
          } else {
            return BinaryExpr.ResolvedOpcode.Gt;
          }
        case BinaryExpr.Opcode.Ge:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Superset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSuperset;
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
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        return cce.NonNull(e.Field).IsGhost || UsesSpecFeatures(e.Obj);
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
               (e.Index != null && UsesSpecFeatures(e.Index)) ||
               (e.Value != null && UsesSpecFeatures(e.Value));
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        if (cce.NonNull(e.Function).IsGhost) {
          return true;
        }
        return e.Args.Exists(arg => UsesSpecFeatures(arg));
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is FreshExpr) {
        return true;
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
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
        var e = (UnaryExpr)expr;
        if (e.Op == UnaryExpr.Opcode.Not) {
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
      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        if (e.Field.EnclosingClass is CoDatatypeDecl) {
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
        if (ModuleDefinition.InSameSCC(currentFunction, e.Function)) {
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
