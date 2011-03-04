//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Resolver {
    public int ErrorCount = 0;
    protected virtual void Error(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Red;
      Console.WriteLine("{0}({1},{2}): Error: {3}",
          tok.filename, tok.line, tok.col-1,
          string.Format(msg, args));
      Console.ForegroundColor = col;
      ErrorCount++;
    }
    void Error(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Error(d.tok, msg, args);
    }
    void Error(Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Error(s.Tok, msg, args);
    }
    void Error(NonglobalVariable v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Error(v.tok, msg, args);
    }
    void Error(Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Error(e.tok, msg, args);
    }

    readonly BuiltIns builtIns;
    readonly Dictionary<string/*!*/,TopLevelDecl/*!*/>/*!*/ classes = new Dictionary<string/*!*/,TopLevelDecl/*!*/>();
    readonly Dictionary<ClassDecl/*!*/,Dictionary<string/*!*/,MemberDecl/*!*/>/*!*/>/*!*/ classMembers = new Dictionary<ClassDecl/*!*/,Dictionary<string/*!*/,MemberDecl/*!*/>/*!*/>();
    readonly Dictionary<DatatypeDecl/*!*/,Dictionary<string/*!*/,DatatypeCtor/*!*/>/*!*/>/*!*/ datatypeCtors = new Dictionary<DatatypeDecl/*!*/,Dictionary<string/*!*/,DatatypeCtor/*!*/>/*!*/>();
    readonly Graph<ModuleDecl/*!*/>/*!*/ importGraph = new Graph<ModuleDecl/*!*/>();

    public Resolver(Program prog) {
      Contract.Requires(prog != null);
      builtIns = prog.BuiltIns;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(builtIns != null);
      Contract.Invariant(cce.NonNullElements(classes));
      Contract.Invariant(cce.NonNullElements(importGraph));
      Contract.Invariant(cce.NonNullElements(classMembers) && Contract.ForAll(classMembers.Values, v => cce.NonNullElements(v)));
      Contract.Invariant(cce.NonNullElements(datatypeCtors) && Contract.ForAll(datatypeCtors.Values, v => cce.NonNullElements(v)));
    }

    bool checkRefinements = true; // used to indicate a cycle in refinements
      
    public void ResolveProgram(Program prog) {
      Contract.Requires(prog != null);
      // register modules
      Dictionary<string,ModuleDecl> modules = new Dictionary<string,ModuleDecl>();
      foreach (ModuleDecl m in prog.Modules) {
        if (modules.ContainsKey(m.Name)) {
          Error(m, "Duplicate module name: {0}", m.Name);
        } else {
          modules.Add(m.Name, m);
        }
      }
      // resolve imports and register top-level declarations
      RegisterTopLevelDecls(prog.BuiltIns.SystemModule.TopLevelDecls);
      Graph<TopLevelDecl> refines = new Graph<TopLevelDecl>();
      foreach (ModuleDecl m in prog.Modules) {
        importGraph.AddVertex(m);
        foreach (string imp in m.Imports) {
          ModuleDecl other;
          if (!modules.TryGetValue(imp, out other)) {
            Error(m, "module {0} named among imports does not exist", imp);
          } else if (other == m) {
            Error(m, "module must not import itself: {0}", imp);
          } else {
            Contract.Assert(other != null);  // follows from postcondition of TryGetValue
            importGraph.AddEdge(m, other);
          }
        }
        RegisterTopLevelDecls(m.TopLevelDecls);
        foreach (TopLevelDecl decl in m.TopLevelDecls) {Contract.Assert(decl != null); refines.AddVertex(decl);}
      }
      // check for cycles in the import graph
      List<ModuleDecl> cycle = importGraph.TryFindCycle();
      if (cycle != null) {
        string cy = "";
        string sep = "";
        foreach (ModuleDecl m in cycle) {
          cy = m.Name + sep + cy;
          sep = " -> ";
        }
        Error(cycle[0], "import graph contains a cycle: {0}", cy);
      } else {
        // fill in module heights
        List<ModuleDecl> mm = importGraph.TopologicallySortedComponents();
        Contract.Assert(mm.Count == prog.Modules.Count);  // follows from the fact that there are no cycles
        int h = 0;
        foreach (ModuleDecl m in mm) {
          m.Height = h;
          h++;
        }
      }

      // resolve top-level declarations of refinements      
      foreach (ModuleDecl m in prog.Modules) 
        foreach (TopLevelDecl decl in m.TopLevelDecls) 
          if (decl is ClassRefinementDecl) {
            ClassRefinementDecl rdecl = (ClassRefinementDecl) decl;
            ResolveTopLevelRefinement(rdecl);
            if (rdecl.Refined != null) refines.AddEdge(rdecl, rdecl.Refined);
          }
      
      // attempt finding refinement cycles
      List<TopLevelDecl> refinesCycle = refines.TryFindCycle();
      if (refinesCycle != null) {
        string cy = "";
        string sep = "";
        foreach (TopLevelDecl decl in refinesCycle) {
          cy = decl + sep + cy;
          sep = " -> ";
        }
        Error(refinesCycle[0], "Detected a cyclic refinement declaration: {0}", cy);
        checkRefinements = false;
      } 
      
      // resolve top-level declarations
      Graph<DatatypeDecl> datatypeDependencies = new Graph<DatatypeDecl>();
      foreach (ModuleDecl m in prog.Modules) {
        ResolveTopLevelDecls_Signatures(m.TopLevelDecls, datatypeDependencies);
      }
      foreach (ModuleDecl m in prog.Modules) {
        ResolveTopLevelDecls_Meat(m.TopLevelDecls, datatypeDependencies);
      }
      // compute IsRecursive bit for mutually recursive functions
      foreach (ModuleDecl m in prog.Modules) {
        foreach (TopLevelDecl decl in m.TopLevelDecls) {
          ClassDecl cl = decl as ClassDecl;
          if (cl != null) {
            foreach (MemberDecl member in cl.Members) {
              Function fn = member as Function;
              if (fn != null && !fn.IsRecursive) {  // note, self-recursion has already been determined
                int n = m.CallGraph.GetSCCSize(fn);
                if (2 <= n) {
                  // the function is mutually recursive (note, the SCC does not determine self recursion)
                  fn.IsRecursive = true;
                }
              }
            }
          }
        }
      }
    }
    
    public void RegisterTopLevelDecls(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        // register the class/datatype name
        if (classes.ContainsKey(d.Name)) {
          Error(d, "Duplicate name of top-level declaration: {0}", d.Name);
        } else {
          classes.Add(d.Name, d);
        }

        if (d is ClassDecl) {
          ClassDecl cl = (ClassDecl)d;

          // register the names of the class members
          Dictionary<string, MemberDecl> members = new Dictionary<string, MemberDecl>();
          classMembers.Add(cl, members);

          foreach (MemberDecl m in cl.Members) {
            if (members.ContainsKey(m.Name)) {
              Error(m, "Duplicate member name: {0}", m.Name);
            } else {
              members.Add(m.Name, m);
            }
          }

        } else {
          DatatypeDecl dt = (DatatypeDecl)d;

          // register the names of the constructors
          Dictionary<string,DatatypeCtor> ctors = new Dictionary<string,DatatypeCtor>();
          datatypeCtors.Add(dt, ctors);
        
          foreach (DatatypeCtor ctor in dt.Ctors) {
            if (ctors.ContainsKey(ctor.Name)) {
              Error(ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
            } else {
              ctors.Add(ctor.Name, ctor);
            }
          }
        }
      }
    }

    public void ResolveTopLevelRefinement(ClassRefinementDecl decl) {
      Contract.Requires(decl != null);
      if (!classes.ContainsKey(decl.RefinedClass.val)) {
        Error(decl.RefinedClass, "Refined class declaration is missing: {0}", decl.RefinedClass.val);
      } else {
        TopLevelDecl a = classes[decl.RefinedClass.val];
        if (!(a is ClassDecl)) {
          Error(a, "Refined declaration is not a class declaration: {0}", a.Name);
          return;
        }
        decl.Refined = cce.NonNull((ClassDecl) a);
        // TODO: copy over remaining members of a
      }        
    }  
      
    public void ResolveTopLevelDecls_Signatures(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<DatatypeDecl/*!*/>/*!*/ datatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies));
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        if (d is ClassDecl) {
          ResolveClassMemberTypes((ClassDecl)d);
        } else {
          ResolveCtorTypes((DatatypeDecl)d, datatypeDependencies);
        }
        allTypeParameters.PopMarker();
      }
    }
    
    public void ResolveTopLevelDecls_Meat(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<DatatypeDecl/*!*/>/*!*/ datatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies));
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        if (d is ClassDecl) {
          ResolveClassMemberBodies((ClassDecl)d);
        } else {
          DatatypeDecl dtd = (DatatypeDecl)d;
          if (datatypeDependencies.GetSCCRepresentative(dtd) == dtd) {
            // do the following check once per SCC, so call it on each SCC representative
            SccStratosphereCheck(dtd, datatypeDependencies);
          }
        }
        allTypeParameters.PopMarker();
      }
    }
    
    ClassDecl currentClass;
    Function currentFunction;
    readonly Scope<TypeParameter>/*!*/ allTypeParameters = new Scope<TypeParameter>();
    readonly Scope<IVariable>/*!*/ scope = new Scope<IVariable>();
    readonly Scope<Statement>/*!*/ labeledStatements = new Scope<Statement>();
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveClassMemberTypes(ClassDecl/*!*/ cl)
    {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);
    
      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        member.EnclosingClass = cl;
        if (member is Field) {
          ResolveType(((Field)member).Type);
          
        } else if (member is Function) {
          Function f = (Function)member;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, true, f);
          ResolveFunctionSignature(f);
          allTypeParameters.PopMarker();

        } else if (member is Method) {
          Method m = (Method)member;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, true, m);
          ResolveMethodSignature(m);
          allTypeParameters.PopMarker();
          
        } else if (member is CouplingInvariant) {
          CouplingInvariant inv = (CouplingInvariant)member;
          if (currentClass is ClassRefinementDecl) {      
            ClassDecl refined = ((ClassRefinementDecl)currentClass).Refined;
            if (refined != null) {
              Contract.Assert(classMembers.ContainsKey(refined));
              Dictionary<string,MemberDecl> members = classMembers[refined];
            
              // resolve abstracted fields in the refined class
              List<Field> fields = new List<Field>();
              foreach (IToken tok in inv.Toks) {
                if (!members.ContainsKey(tok.val))
                  Error(tok, "Refined class does not declare a field: {0}", tok.val);
                else {
                  MemberDecl field = members[tok.val];
                  if (!(field is Field)) 
                    Error(tok, "Coupling invariant refers to a non-field member: {0}", tok.val);
                  else if (fields.Contains(cce.NonNull((Field)field)))
                    Error(tok, "Duplicate reference to a field in the refined class: {0}", tok.val);
                  else
                    fields.Add(cce.NonNull((Field)field));
                }                  
              }            
              inv.Refined = fields;
            }
            
          } else {
            Error(member, "Coupling invariants can only be declared in refinement classes");
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
        
        if (currentClass is ClassRefinementDecl) {          
          ClassDecl refined = ((ClassRefinementDecl)currentClass).Refined;
          if (refined != null) {
            Contract.Assert(classMembers.ContainsKey(refined));
          
            // there is a member with the same name in refined class if and only if the member is a refined method
            if ((member is MethodRefinement) != (classMembers[refined].ContainsKey(member.Name)))
              Error(member, "Refined class has a member with the same name as in the refinement class: {0}", member.Name);
          }
        }
      }
      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed, and that all types in class members have been resolved
    /// </summary>
    void ResolveClassMemberBodies(ClassDecl cl)
    {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);
    
      ResolveAttributes(cl.Attributes, false);
      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        ResolveAttributes(member.Attributes, false);
        if (member is Field) {
          // nothing more to do
          
        } else if (member is Function) {
          Function f = (Function)member;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, false, f);
          ResolveFunction(f);
          allTypeParameters.PopMarker();

        } else if (member is Method) {
          Method m = (Method)member;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, false, m);
          ResolveMethod(m);
          allTypeParameters.PopMarker();
          
          // check if signature of the refined method matches the refinement method
          if (member is MethodRefinement) {
            MethodRefinement mf = (MethodRefinement)member;
            if (currentClass is ClassRefinementDecl) {
              // should have already been resolved
              if (((ClassRefinementDecl)currentClass).Refined != null) { 
                MemberDecl d = classMembers[((ClassRefinementDecl)currentClass).Refined][mf.Name];
                if (d is Method) {
                  mf.Refined = (Method)d;
                  if (mf.Ins.Count != mf.Refined.Ins.Count)
                    Error(mf, "Different number of input variables");
                  if (mf.Outs.Count != mf.Refined.Outs.Count)
                    Error(mf, "Different number of output variables");
                  if (mf.IsStatic || mf.Refined.IsStatic) 
                    Error(mf, "Refined methods cannot be static");
                } else {
                  Error(member, "Refined class has a non-method member with the same name: {0}", member.Name);
                }            
              }
            } else {
              Error(member, "Refinement methods can only be declared in refinement classes: {0}", member.Name);
            }
          }
        
        } else if (member is CouplingInvariant) {        
          CouplingInvariant inv = (CouplingInvariant)member;
          if (inv.Refined != null) {
            inv.Formals = new List<Formal>();
            scope.PushMarker();
            for (int i = 0; i < inv.Refined.Count; i++) {
              Field field = inv.Refined[i];
              Contract.Assert(field != null);
              Formal formal = new Formal(inv.Toks[i], field.Name, field.Type, true, field.IsGhost);
              Contract.Assert(formal != null);
              inv.Formals.Add(formal);
              scope.Push(inv.Toks[i].val, formal);
            }
            ResolveExpression(inv.Expr, false, true);
            scope.PopMarker();
          }                
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }
      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveCtorTypes(DatatypeDecl/*!*/ dt, Graph<DatatypeDecl/*!*/>/*!*/ dependencies)
    {
      Contract.Requires(dt != null);
      Contract.Requires(cce.NonNullElements(dependencies));
      foreach (DatatypeCtor ctor in dt.Ctors) {
        
        ctor.EnclosingDatatype = dt;

        allTypeParameters.PushMarker();
        ResolveTypeParameters(ctor.TypeArgs, true, ctor);
        ResolveCtorSignature(ctor);
        allTypeParameters.PopMarker();
        
        foreach (Formal p in ctor.Formals) {
          DatatypeDecl dependee = p.Type.AsDatatype;
          if (dependee != null) {
            dependencies.AddEdge(dt, dependee);
          }
        }
      }
    }

    /// <summary>
    /// Check that the SCC of 'startingPoint' can be carved up into stratospheres in such a way that each
    /// datatype has some value that can be constructed from datatypes in lower stratospheres only.
    /// The algorithm used here is quadratic in the number of datatypes in the SCC.  Since that number is
    /// deemed to be rather small, this seems okay.
    /// </summary>    
    void SccStratosphereCheck(DatatypeDecl startingPoint, Graph<DatatypeDecl/*!*/>/*!*/ dependencies)
    {
      Contract.Requires(startingPoint != null);
      Contract.Requires(cce.NonNullElements(dependencies));
      List<DatatypeDecl> scc = dependencies.GetSCC(startingPoint);
      List<DatatypeDecl> cleared = new List<DatatypeDecl>();  // this is really a set
      while (true) {
        int clearedThisRound = 0;
        foreach (DatatypeDecl dt in scc) {
          if (cleared.Contains(dt)) {
            // previously cleared
          } else if (StratosphereCheck(dt, dependencies, cleared)) {
            clearedThisRound++;
            cleared.Add(dt);
            // (it would be nice if the List API allowed us to remove 'dt' from 'scc' here; then we wouldn't have to check 'cleared.Contains(dt)' above and below)
          }
        }
        if (cleared.Count == scc.Count) {
          // all is good
          return;
        } else if (clearedThisRound != 0) {
          // some progress was made, so let's keep going
        } else {
          // whatever is in scc-cleared now failed to pass the test
          foreach (DatatypeDecl dt in scc) {
            if (!cleared.Contains(dt)) {
              Error(dt, "because of cyclic dependencies among constructor argument types, no instances of datatype '{0}' can be constructed", dt.Name);
            }
          }
          return;
        }
      }
    }

    /// <summary>
    /// Check that the datatype has some constructor all whose argument types go to a lower stratum, which means
    /// go to a different SCC or to a type in 'goodOnes'.
    /// Returns 'true' and sets dt.DefaultCtor if that is the case.
    /// </summary>
    bool StratosphereCheck(DatatypeDecl dt, Graph<DatatypeDecl/*!*/>/*!*/ dependencies, List<DatatypeDecl/*!*/>/*!*/ goodOnes) {
      Contract.Requires(dt != null);
      Contract.Requires(cce.NonNullElements(dependencies));
      Contract.Requires(cce.NonNullElements(goodOnes));
      // Stated differently, check that there is some constuctor where no argument type goes to the same stratum.
      DatatypeDecl stratumRepresentative = dependencies.GetSCCRepresentative(dt);
      foreach (DatatypeCtor ctor in dt.Ctors) {
        foreach (Formal p in ctor.Formals) {
          DatatypeDecl dependee = p.Type.AsDatatype;
          if (dependee == null) {
            // the type is not a datatype, which means it's in the lowest stratum (below all datatypes)
          } else if (dependencies.GetSCCRepresentative(dependee) != stratumRepresentative) {
            // the argument type goes to a different stratum, which must be a "lower" one, so this argument is fine
          } else if (goodOnes.Contains(dependee)) {
            // the argument type is in the same SCC, but has already passed the test, so it is to be considered as
            // being in a lower stratum
          } else {
            // the argument type is in the same stratum as 'dt', so this constructor is not what we're looking for
            goto NEXT_OUTER_ITERATION;
          }
        }
        // this constructor satisfies the requirements, so the datatype is allowed
        dt.DefaultCtor = ctor;
        return true;
        NEXT_OUTER_ITERATION: {}
      }
      // no constructor satisfied the requirements, so this is an illegal datatype declaration
      return false;
    }

    void ResolveAttributes(Attributes attrs, bool twoState) {
      // order does not matter for resolution, so resolve them in reverse order
      for (; attrs != null; attrs = attrs.Prev) {
        ResolveAttributeArgs(attrs.Args, twoState, true);
      }
    }
        
    void ResolveAttributeArgs(List<Attributes.Argument/*!*/>/*!*/ args, bool twoState, bool specContext) {
      Contract.Requires(args != null);
      foreach (Attributes.Argument aa in args) {
        Contract.Assert(aa != null);
        if (aa.E != null) {
          ResolveExpression(aa.E, twoState, specContext);
        }
      }
    }
        
    void ResolveTriggers(Triggers trigs, bool twoState) {
      // order does not matter for resolution, so resolve them in reverse order
      for (; trigs != null; trigs = trigs.Prev) {
        foreach (Expression e in trigs.Terms) {
          ResolveExpression(e, twoState, true);
        }
      }
    }
        
    void ResolveTypeParameters(List<TypeParameter/*!*/>/*!*/ tparams, bool emitErrors, TypeParameter.ParentType/*!*/ parent) {
      
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push type arguments of the refined class
      if (checkRefinements && parent is ClassRefinementDecl) {
        ClassDecl refined = ((ClassRefinementDecl)parent).Refined;
        if (refined != null)
          ResolveTypeParameters(refined.TypeArgs, false, refined);
      }
    
      // push non-duplicated type parameter names
      foreach (TypeParameter tp in tparams) {
        Contract.Assert(tp != null);
        if (emitErrors) {
          // we're seeing this TypeParameter for the first time
          tp.Parent = parent;
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
      foreach (Formal p in f.Formals) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.Type);
      }
      ResolveType(f.ResultType);
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunction(Function f){
      Contract.Requires(f != null);
      Contract.Requires(currentFunction == null);
      Contract.Ensures(currentFunction == null);
      scope.PushMarker();
      currentFunction = f;
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }
      foreach (Formal p in f.Formals) {
        scope.Push(p.Name, p);
      }
      foreach (Expression r in f.Req) {
        ResolveExpression(r, false, true);
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Precondition must be a boolean (got {0})", r.Type);
        }
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, "reads");
      }
      foreach (Expression r in f.Ens) {
        ResolveExpression(r, false, true);  // since this is a function, the postcondition is still a one-state predicate
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(r.Type, Type.Bool)) {
          Error(r, "Postcondition must be a boolean (got {0})", r.Type);
        }
      }
      foreach (Expression r in f.Decreases) {
        ResolveExpression(r, false, true);
        // any type is fine
      }
      if (f.Body != null) {
        List<IVariable> matchVarContext = new List<IVariable>(f.Formals);
        ResolveExpression(f.Body, false, f.IsGhost, matchVarContext);
        Contract.Assert(f.Body.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(f.Body.Type, f.ResultType)) {
          Error(f, "Function body type mismatch (expected {0}, got {1})", f.ResultType, f.Body.Type);
        }
      }
      currentFunction = null;
      scope.PopMarker();
    }
    
    void ResolveFrameExpression(FrameExpression fe, string kind) {
      Contract.Requires(fe != null);
      Contract.Requires(kind != null);
      ResolveExpression(fe.E, false, true);
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      if (t is CollectionType) {
        t = ((CollectionType)t).Arg;
      }
      if (t is ObjectType) {
        // fine, as long as there's no field name
        if (fe.FieldName != null) {
          Error(fe.E, "type '{0}' does not contain a field named '{1}'", t, fe.FieldName);
        }
      } else if (UserDefinedType.DenotesClass(t) != null) {
        // fine type
        if (fe.FieldName != null) {
          UserDefinedType ctype;
          MemberDecl member = ResolveMember(fe.E.tok, t, fe.FieldName, out ctype);
          if (member == null) {
            // error has already been reported by ResolveMember
          } else if (!(member is Field)) {
            Error(fe.E, "member {0} in class {1} does not refer to a field", fe.FieldName, cce.NonNull(ctype).Name);
          } else {
            Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
            fe.Field = (Field)member;
          }
        }
      } else {
        Error(fe.E, "a {0}-clause expression must denote an object or a collection of objects (instead got {1})", kind, fe.E.Type);
      }
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethodSignature(Method m) {
      Contract.Requires(m != null);
      scope.PushMarker();
      // resolve in-parameters
      foreach (Formal p in m.Ins) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.Type);
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.Type);
      }
      scope.PopMarker();
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);
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
        ResolveExpression(e.E, false, true);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Precondition must be a boolean (got {0})", e.E.Type);
        }
      }
      foreach (FrameExpression fe in m.Mod) {
        ResolveFrameExpression(fe, "modifies");
      }
      foreach (Expression e in m.Decreases) {
        ResolveExpression(e, false, true);
        // any type is fine
      }
      
      // Add out-parameters to a new scope that will also include the outermost-level locals of the body
      // Don't care about any duplication errors among the out-parameters, since they have already been reported
      scope.PushMarker();
      foreach (Formal p in m.Outs) {
        scope.Push(p.Name, p);
      }

      // ... continue resolving specification
      foreach (MaybeFreeExpression e in m.Ens) {
        ResolveExpression(e.E, true, true);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E.Type, Type.Bool)) {
          Error(e.E, "Postcondition must be a boolean (got {0})", e.E.Type);
        }
      }
      
      // Resolve body
      if (m.Body != null) {
        ResolveBlockStatement(m.Body, m.IsGhost, m);
      }
      
      scope.PopMarker();  // for the out-parameters and outermost-level locals
      scope.PopMarker();  // for the in-parameters
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveCtorSignature(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      scope.PushMarker();
      foreach (Formal p in ctor.Formals) {
        if (!scope.Push(p.Name, p)) {
          Error(p, "Duplicate parameter name: {0}", p.Name);
        }
        ResolveType(p.Type);
      }
      scope.PopMarker();
    }

    public void ResolveType(Type type) {
      Contract.Requires(type != null);
      if (type is BasicType) {
        // nothing to resolve
      } else if (type is CollectionType) {
        ResolveType(((CollectionType)type).Arg);
      } else if (type is UserDefinedType) {
        UserDefinedType t = (UserDefinedType)type;
        foreach (Type tt in t.TypeArgs) {
          ResolveType(tt);
        }
        TypeParameter tp = allTypeParameters.Find(t.Name);
        if (tp != null) {
          if (t.TypeArgs.Count == 0) {
            t.ResolvedParam = tp;
          } else {
            Error(t.tok, "Type parameter expects no type arguments: {0}", t.Name);
          }
        } else if (t.ResolvedClass == null) {  // this test is becausee 'array' is already resolved; TODO: an alternative would be to pre-populate 'classes' with built-in references types like 'array' (and perhaps in the future 'string')
          TopLevelDecl d;
          if (!classes.TryGetValue(t.Name, out d)) {
            Error(t.tok, "Undeclared top-level type or type parameter: {0}", t.Name);
          } else if (cce.NonNull(d).TypeArgs.Count == t.TypeArgs.Count) {
            t.ResolvedClass = d;
          } else {
            Error(t.tok, "Wrong number of type arguments ({0} instead of {1}) passed to class/datatype: {2}", t.TypeArgs.Count, d.TypeArgs.Count, t.Name);
          }
        }
      
      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(t.T);
        }
        
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
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
        // allow anything with object; this is BOGUS
        return true;
      }
#endif
      // Now, a and b are non-proxies and stand for the same things as the original a and b, respectively.
      
      if (a is BoolType) {
        return b is BoolType;
      } else if (a is IntType) {
        return b is IntType;
      } else if (a is ObjectType) {
        return b is ObjectType;
      } else if (a is SetType) {
        return b is SetType && UnifyTypes(((SetType)a).Arg, ((SetType)b).Arg);
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
    
    bool AssignProxy(TypeProxy proxy, Type t){
      Contract.Requires(proxy != null);
      Contract.Requires(t != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires((t is TypeProxy)|| ((TypeProxy)t).T == null);
      //modifies proxy.T, ((TypeProxy)t).T;  // might also change t.T if t is a proxy
      Contract.Ensures(Contract.Result<bool>() || proxy == t || proxy.T != null || (t is TypeProxy && ((TypeProxy)t).T != null));
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
        if (t.IsDatatype) {
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
      
      } else if (proxy is ObjectsTypeProxy) {
        if (t is ObjectType || UserDefinedType.DenotesClass(t) != null) {
          // all is good
        } else if (t is CollectionType) {
          proxy.T = new CollectionTypeProxy(new ObjectTypeProxy());
          return UnifyTypes(proxy.T, t);
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
        if (t is IntType || t is SetType || (opProxy.AllowSeq && t is SeqType)) {
          // this is the expected case
        } else {
          return false;
        }

      } else if (proxy is IndexableTypeProxy) {
        IndexableTypeProxy iProxy = (IndexableTypeProxy)proxy;
        if (t is SeqType) {
          if (!UnifyTypes(iProxy.Arg, ((SeqType)t).Arg)) {
            return false;
          }
        } else if (t.IsArrayType) {
          Type elType = UserDefinedType.ArrayElementType(t);
          if (!UnifyTypes(iProxy.Arg, elType)) {
            return false;
          }
        } else {
          return false;
        }
                
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected proxy type
      }
      
      // do the merge
      proxy.T = t;
      return true;
    }
    
    bool AssignRestrictedProxies(RestrictedTypeProxy a, RestrictedTypeProxy b)
    { Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a != b);
      Contract.Requires(a.T == null && b.T == null);
      Contract.Requires(a.OrderID <= b.OrderID);
      //modifies a.T, b.T;
      Contract.Ensures(Contract.Result<bool>() || a.T != null || b.T != null);
    
      if (a is DatatypeProxy) {
        if (b is DatatypeProxy) {
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
        } else if (b is ObjectsTypeProxy) {
          // unify a and b by redirecting b to a, since a gives the stronger requirement
          b.T = a;
          return true;
        } else if (b is IndexableTypeProxy) {
          // the intersection of ObjectTypeProxy and IndexableTypeProxy is an array type
          a.T = builtIns.ArrayType(1, ((IndexableTypeProxy)b).Arg);
          b.T = a.T;
          return true;
        } else {
          return false;
        }
        
      } else if (a is ObjectsTypeProxy) {
        if (b is ObjectsTypeProxy) {
          // fine
          a.T = b;
          return true;
        } else if (b is CollectionTypeProxy) {
          // fine provided b's collection-element-type can be unified with object or a class type
          a.T = b;
          return UnifyTypes(((CollectionTypeProxy)b).Arg, new ObjectTypeProxy());
        } else if (b is OperationTypeProxy) {
          // fine; restrict a to sets of object/class, and restrict b to set/seq of object/class
          if (((OperationTypeProxy)b).AllowSeq) {
            a.T = new CollectionTypeProxy(new ObjectTypeProxy());
            b.T = a.T;
          } else {
            a.T = new SetType(new ObjectTypeProxy());
            b.T = a.T;
          }
          return true;
        } else if (b is IndexableTypeProxy) {
          IndexableTypeProxy pb = (IndexableTypeProxy)b;
          // the intersection of ObjectsTypeProxy and IndexableTypeProxy is
          // EITHER a sequence of ObjectTypeProxy OR an array of anything
          // TODO: here, only the first of the two cases is supported
          b.T = new SeqType(pb.Arg);
          a.T = b.T;
          return UnifyTypes(pb.Arg, new ObjectTypeProxy());
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
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
          IndexableTypeProxy pb = (IndexableTypeProxy)b;
          // strengthen a and b to a sequence type
          a.T = new SeqType(pa.Arg);
          b.T = new SeqType(pb.Arg);
          return UnifyTypes(pa.Arg, pb.Arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
        }
        
      } else if (a is OperationTypeProxy) {
        OperationTypeProxy pa = (OperationTypeProxy)a;
        if (b is OperationTypeProxy) {
          if (!pa.AllowSeq || ((OperationTypeProxy)b).AllowSeq) {
            b.T = a;
          } else {
            a.T = b;  // b has the stronger requirement
          }
          return true;
        } else {
          IndexableTypeProxy pb = (IndexableTypeProxy)b;  // cast justification:  lse we have unexpected restricted-proxy type
          if (pa.AllowSeq) {
            // strengthen a and b to a sequence type
            b.T = new SeqType(pb.Arg);
            a.T = b.T;
            return true;
          } else {
            return false;
          }
        }
        
      } else if (a is IndexableTypeProxy) {
        Contract.Assert(b is IndexableTypeProxy);  // else we have unexpected restricted-proxy type
        a.T = b;
        return UnifyTypes(((IndexableTypeProxy)a).Arg, ((IndexableTypeProxy)b).Arg);
        
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected restricted-proxy type
      }
    }
    
    public void ResolveStatement(Statement stmt, bool specContextOnly, Method method){Contract.Requires(stmt != null);Contract.Requires(method != null);
     Contract.Requires(!(stmt is LabelStmt));  // these should be handled inside lists of statements
      if (stmt is UseStmt) {
        UseStmt s = (UseStmt)stmt;
        s.IsGhost = true;
        ResolveExpression(s.Expr, true, true);
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        Expression expr = s.Expr;
        while (true) {
          if (expr is OldExpr) {
            expr = ((OldExpr)expr).E;
          } else {
            break;
          }
        }
      } else if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        s.IsGhost = true;
        ResolveExpression(s.Expr, true, true);
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Expr.Type, Type.Bool)) {
          Error(s.Expr, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Expr.Type);
        }
      
      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        ResolveAttributeArgs(s.Args, false, false);
          
      } else if (stmt is BreakStmt) {
        BreakStmt s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = labeledStatements.Find(s.TargetLabel);
          if (target == null) {
            Error(s, "break label is undefined or not in scope: {0}", s.TargetLabel);
          } else {
            s.TargetStmt = target;
          }
        }
        if (specContextOnly) {
          Error(stmt, "break statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
        }

      } else if (stmt is ReturnStmt) {
        if (specContextOnly) {
          Error(stmt, "return statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
        }
        
      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        int prevErrorCount = ErrorCount;
        if (s.Lhs is SeqSelectExpr) {
          ResolveSeqSelectExpr((SeqSelectExpr)s.Lhs, true, false, true);
        } else {
          ResolveExpression(s.Lhs, true, true);  // allow ghosts for now, but see FieldSelectExpr LHS case below
        }
        bool lhsResolvedSuccessfully = ErrorCount == prevErrorCount;
        Contract.Assert(s.Lhs.Type != null);  // follows from postcondition of ResolveExpression
        // check that LHS denotes a mutable variable or a field
        bool lvalueIsGhost = false;
        if (s.Lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)s.Lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            lvalueIsGhost = var.IsGhost;
            if (!var.IsMutable) {
              Error(stmt, "LHS of assignment must denote a mutable variable or field");
            }
          }
        } else if (s.Lhs is FieldSelectExpr) {
          // LHS is fine, but restrict the RHS to ExprRhs
          if (!(s.Rhs is ExprRhs)) {
            Error(stmt, "Assignment to field must have an expression RHS; try using a temporary local variable");
          } else {
            FieldSelectExpr fse = (FieldSelectExpr)s.Lhs;
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
              if (!fse.Field.IsMutable) {
                Error(stmt, "LHS of assignment does not denote a mutable field");
              }
            }
          }
        } else if (s.Lhs is SeqSelectExpr) {
          SeqSelectExpr lhs = (SeqSelectExpr)s.Lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(lhs.Seq.Type != null);
            Type elementType = new InferredTypeProxy();
            if (!UnifyTypes(lhs.Seq.Type, builtIns.ArrayType(1, elementType))) {
              Error(lhs.Seq, "LHS of array assignment must denote an array element (found {0})", lhs.Seq.Type);
            }
            if (specContextOnly) {
              Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
            }
          }
          if (!(s.Rhs is ExprRhs)) {
            Error(stmt, "Assignment to array element must have an expression RHS; try using a temporary local variable");
          }

        } else if (s.Lhs is MultiSelectExpr) {
          if (specContextOnly) {
            Error(stmt, "Assignment to array element is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          }
          if (!(s.Rhs is ExprRhs)) {
            Error(stmt, "Assignment to array element must have an expression RHS; try using a temporary local variable");
          }

        } else {
          Error(stmt, "LHS of assignment must denote a mutable variable or field");
        }
        
        s.IsGhost = lvalueIsGhost;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, true, lvalueIsGhost);
          Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression
          Type lhsType = s.Lhs.Type;
          if (s.Lhs is SeqSelectExpr && !((SeqSelectExpr)s.Lhs).SelectOne) {
            Contract.Assert(lhsType.IsArrayType);
            lhsType = UserDefinedType.ArrayElementType(lhsType);
          }
          if (!UnifyTypes(lhsType, rr.Expr.Type)) {
            Error(stmt, "RHS (of type {0}) not assignable to LHS (of type {1})", rr.Expr.Type, s.Lhs.Type);
          }
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          Type t = ResolveTypeRhs(rr, stmt, lvalueIsGhost);
          if (!UnifyTypes(s.Lhs.Type, t)) {
            Error(stmt, "type {0} is not assignable to LHS (of type {1})", t, s.Lhs.Type);
          }
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }
        
      } else if (stmt is VarDecl) {
        VarDecl s = (VarDecl)stmt;
        if (s.OptionalType != null) {
          ResolveType(s.OptionalType);
          s.type = s.OptionalType;
        }
        if (s.Rhs != null) {
          Type rhsType;
          if (s.Rhs is ExprRhs) {
            ExprRhs rr = (ExprRhs)s.Rhs;
            ResolveExpression(rr.Expr, true, s.IsGhost);
            Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression
            rhsType = rr.Expr.Type;
          } else if (s.Rhs is TypeRhs) {
            TypeRhs rr = (TypeRhs)s.Rhs;
            rhsType = ResolveTypeRhs(rr, stmt, s.IsGhost);
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
          }
          if (s.OptionalType == null) {
            s.type = rhsType;
          } else if (!UnifyTypes(s.OptionalType, rhsType)) {
            Error(stmt, "initialization RHS (of type {0}) not assignable to variable (of type {1})", rhsType, s.OptionalType);
          }
        }
        // now that the declaration has been processed, add the name to the scope
        if (!scope.Push(s.Name, s)) {
          Error(s, "Duplicate local-variable name: {0}", s.Name);
        }
      
      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;

        // resolve receiver
        ResolveReceiver(s.Receiver, true, false);
        Contract.Assert(s.Receiver.Type != null);  // follows from postcondition of ResolveExpression
        // resolve the method name
        UserDefinedType ctype;
        MemberDecl member = ResolveMember(s.Tok, s.Receiver.Type, s.MethodName, out ctype);
        Method callee = null;
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Method)) {
          Error(s, "member {0} in class {1} does not refer to a method", s.MethodName, cce.NonNull(ctype).Name);
        } else {
          callee = (Method)member;
          s.Method = callee;
          s.IsGhost = callee.IsGhost;
          if (specContextOnly && !callee.IsGhost) {
            Error(s, "only ghost methods can be called from this context");
          }
        }

        // resolve any local variables declared here
        foreach (AutoVarDecl local in s.NewVars) {
          // first, fix up the local variables to be ghost variable if the corresponding formal out-parameter is a ghost
          if (s.IsGhost || callee != null && local.Index < callee.Outs.Count && callee.Outs[local.Index].IsGhost) {
            local.MakeGhost();
          }
          ResolveStatement(local, specContextOnly, method);
        }
        
        // resolve left-hand side
        Dictionary<string,object> lhsNameSet = new Dictionary<string,object>();
        foreach (IdentifierExpr lhs in s.Lhs) {
          ResolveExpression(lhs, true, true);
          if (lhsNameSet.ContainsKey(lhs.Name)) {
            Error(s, "Duplicate variable in left-hand side of call statement: {0}", lhs.Name);
          } else {
            lhsNameSet.Add(lhs.Name, null);
          }
        }
        // resolve arguments
        int j = 0;
        foreach (Expression e in s.Args) {
          bool allowGhost = s.IsGhost || callee == null || callee.Ins.Count <= j || callee.Ins[j].IsGhost;
          ResolveExpression(e, true, allowGhost);
          j++;
        }
        
        if (callee == null) {
          // error has been reported above
        } else if (callee.Ins.Count != s.Args.Count) {
          Error(s, "wrong number of method arguments (got {0}, expected {1})", s.Args.Count, callee.Ins.Count);
        } else if (callee.Outs.Count != s.Lhs.Count) {
          Error(s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
        } else {
          Contract.Assert(ctype != null);  // follows from postcondition of ResolveMember above
          if (!scope.AllowInstance && !callee.IsStatic && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            Error(s.Receiver, "'this' is not allowed in a 'static' context");
          }
          // build the type substitution map
          Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
          for (int i = 0; i < ctype.TypeArgs.Count; i++) {
            subst.Add(cce.NonNull(ctype.ResolvedClass).TypeArgs[i], ctype.TypeArgs[i]);
          }
          foreach (TypeParameter p in callee.TypeArgs) {
            subst.Add(p, new ParamTypeProxy(p));
          }
          // type check the arguments
          for (int i = 0; i < callee.Ins.Count; i++) {
            Type st = SubstType(callee.Ins[i].Type, subst);
            if (!UnifyTypes(cce.NonNull(s.Args[i].Type), st)) {
              Error(s, "incorrect type of method in-parameter {0} (expected {1}, got {2})", i, st, s.Args[i].Type);
            }
          }
          for (int i = 0; i < callee.Outs.Count; i++) {
            Type st = SubstType(callee.Outs[i].Type, subst);
            IdentifierExpr lhs = s.Lhs[i];
            if (!UnifyTypes(cce.NonNull(lhs.Type), st)) {
              Error(s, "incorrect type of method out-parameter {0} (expected {1}, got {2})", i, st, lhs.Type);
            } else if (!specContextOnly && !cce.NonNull(lhs.Var).IsGhost && (s.IsGhost || callee.Outs[i].IsGhost)) {
              Error(s, "actual out-parameter {0} is required to be a ghost variable", i);
            }
          }
          
          // Resolution termination check
          if (method.EnclosingClass != null && callee.EnclosingClass != null) {
            ModuleDecl callerModule = method.EnclosingClass.Module;
            ModuleDecl calleeModule = callee.EnclosingClass.Module;
            if (callerModule == calleeModule) {
              // intra-module call; this is allowed; add edge in module's call graph
              callerModule.CallGraph.AddEdge(method, callee);
            } else if (calleeModule.IsDefaultModule) {
              // all is fine: everything implicitly imports the default module
            } else if (importGraph.Reaches(callerModule, calleeModule)) {
              // all is fine: the callee is downstream of the caller
            } else {
              Error(s, "inter-module calls must follow the module import relation (so module {0} must transitively import {1})", callerModule.Name, calleeModule.Name);
            }
          }
        }
        
      } else if (stmt is BlockStmt) {
        scope.PushMarker();
        ResolveBlockStatement((BlockStmt)stmt, specContextOnly, method);
        scope.PopMarker();
      
      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        bool branchesAreSpecOnly = specContextOnly;
        if (s.Guard != null) {
          int prevErrorCount = ErrorCount;
          ResolveExpression(s.Guard, true, true);
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
        ResolveStatement(s.Thn, branchesAreSpecOnly, method);
        if (s.Els != null) {
          ResolveStatement(s.Els, branchesAreSpecOnly, method);
        }
      
      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        bool bodyIsSpecOnly = specContextOnly;
        if (s.Guard != null) {
          int prevErrorCount = ErrorCount;
          ResolveExpression(s.Guard, true, true);
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          bool successfullyResolved = ErrorCount == prevErrorCount;
          if (!UnifyTypes(s.Guard.Type, Type.Bool)) {
            Error(s.Guard, "condition is expected to be of type {0}, but is {1}", Type.Bool, s.Guard.Type);
          }
          if (!specContextOnly && successfullyResolved) {
            bodyIsSpecOnly = UsesSpecFeatures(s.Guard);
          }
        }
        foreach (MaybeFreeExpression inv in s.Invariants) {
          ResolveExpression(inv.E, true, true);
          Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(inv.E.Type, Type.Bool)) {
            Error(inv.E, "invariant is expected to be of type {0}, but is {1}", Type.Bool, inv.E.Type);
          }
        }
        foreach (Expression e in s.Decreases) {
          ResolveExpression(e, true, true);
          // any type is fine
        }
        s.IsGhost = bodyIsSpecOnly;
        ResolveStatement(s.Body, bodyIsSpecOnly, method);
      
      } else if (stmt is ForeachStmt) {
        ForeachStmt s = (ForeachStmt)stmt;

        ResolveExpression(s.Collection, true, true);
        Contract.Assert(s.Collection.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Collection.Type, new CollectionTypeProxy(s.BoundVar.Type))) {
          Error(s.Collection, "The type is expected to be a collection of {0} (instead got {1})", s.BoundVar.Type, s.Collection.Type);
        }
        
        scope.PushMarker();
        bool b = scope.Push(s.BoundVar.Name, s.BoundVar);
        Contract.Assert(b);  // since we just pushed a marker, we expect the Push to succeed
        ResolveType(s.BoundVar.Type);
        int prevErrorCount = ErrorCount;
        
        ResolveExpression(s.Range, true, true);
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(s.Range.Type, Type.Bool)) {
          Error(s.Range, "range condition is expected to be of type {0}, but is {1}", Type.Bool, s.Range.Type);
        }
        bool successfullyResolvedCollectionAndRange = ErrorCount == prevErrorCount;
        
        foreach (PredicateStmt ss in s.BodyPrefix) {
          ResolveStatement(ss, specContextOnly, method);
        }

        bool specOnly = specContextOnly ||
                        (successfullyResolvedCollectionAndRange && (UsesSpecFeatures(s.Collection) || UsesSpecFeatures(s.Range)));
        s.IsGhost = specOnly;
        ResolveStatement(s.BodyAssign, specOnly, method);
        // check for correct usage of BoundVar in LHS and RHS of this assignment
        FieldSelectExpr lhs = s.BodyAssign.Lhs as FieldSelectExpr;
        IdentifierExpr obj = lhs == null ? null : lhs.Obj as IdentifierExpr;
        if (obj != null && obj.Var == s.BoundVar) {
          // exemplary!
        } else {
          Error(s, "assignment inside foreach must assign to a field of the bound variable of the foreach statement");
        }

        scope.PopMarker();
      
      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        bool bodyIsSpecOnly = specContextOnly;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Source, true, true);
        Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = ErrorCount == prevErrorCount;
        if (!specContextOnly && successfullyResolved) {
          bodyIsSpecOnly = UsesSpecFeatures(s.Source);
        }
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
        if (s.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)s.Source.Type;
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
        Dictionary<string,DatatypeCtor> ctors;
        if (dtd == null) {
          Error(s.Source, "the type of the match source expression must be a datatype");
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
        
        Dictionary<string,object> memberNamesUsed = new Dictionary<string,object>();  // this is really a set
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
                Error(mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", mc.Arguments.Count, ctor.Formals.Count);
              }
              if (memberNamesUsed.ContainsKey(mc.Id)) {
                Error(mc.tok, "member {0} appears in more than one case", mc.Id);
              } else {
                memberNamesUsed.Add(mc.Id, null);  // add mc.Id to the set of names used
              }
            }
          }
          scope.PushMarker();
          if (ctor != null) {
            // add the constructor's own type parameters to the substitution map
            foreach (TypeParameter p in ctor.TypeArgs) {
              subst.Add(p, new ParamTypeProxy(p));
            }
          }
          int i = 0;
          foreach (BoundVar v in mc.Arguments) {
            if (!scope.Push(v.Name, v)) {
              Error(v, "Duplicate parameter name: {0}", v.Name);
            }
            ResolveType(v.Type);
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
            ResolveStatement(ss, bodyIsSpecOnly, method);
          }
          scope.PopMarker();
        }
        if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
          Error(stmt, "match expression does not cover all constructors");
        }
        
        
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }
    
    void ResolveBlockStatement(BlockStmt blockStmt, bool specContextOnly, Method method)
    {
      Contract.Requires(blockStmt != null);
      Contract.Requires(method != null);
      int labelsToPop = 0;
      foreach (Statement ss in blockStmt.Body) {
        if (ss is LabelStmt) {
          LabelStmt ls = (LabelStmt)ss;
          labeledStatements.PushMarker();
          bool b = labeledStatements.Push(ls.Label, ls);
          Contract.Assert(b);  // since we just pushed a marker, we expect the Push to succeed
          labelsToPop++;
        } else {
          ResolveStatement(ss, specContextOnly, method);
          for (; 0 < labelsToPop; labelsToPop--) { labeledStatements.PopMarker(); }
        }
      }
      for (; 0 < labelsToPop; labelsToPop--) { labeledStatements.PopMarker(); }
    }

    Type ResolveTypeRhs(TypeRhs rr, Statement stmt, bool specContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      ResolveType(rr.EType);
      if (rr.ArrayDimensions == null) {
        if (!rr.EType.IsRefType) {
          Error(stmt, "new can be applied only to reference types (got {0})", rr.EType);
        }
        return rr.EType;
      } else {
        int i = 0;
        foreach (Expression dim in rr.ArrayDimensions) {
          Contract.Assert(dim != null);
          ResolveExpression(dim, true, specContext);
          if (!UnifyTypes(dim.Type, Type.Int)) {
            Error(stmt, "new must use an integer expression for the array size (got {0} for index {1})", dim.Type, i);
          }
          i++;
        }
        return builtIns.ArrayType(rr.ArrayDimensions.Count, rr.EType);
      }
    }

    MemberDecl ResolveMember(IToken tok, Type receiverType, string memberName, out UserDefinedType ctype)
    {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out ctype) != null && ctype.ResolvedClass != null);
    
      ctype = UserDefinedType.DenotesClass(receiverType);
      if (ctype == null) {
        Error(tok, "receiver (of type {0}) must be of a class type", receiverType);
      } else {
        Contract.Assert(ctype.ResolvedClass is ClassDecl);  // follows from postcondition of DenotesClass
        Contract.Assert(ctype.TypeArgs.Count == ctype.ResolvedClass.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[(ClassDecl)ctype.ResolvedClass].TryGetValue(memberName, out member)) {
          Error(tok, "member {0} does not exist in class {1}", memberName, ctype.Name);
        } else {
          return cce.NonNull(member);
        }
      }
      ctype = null;
      return null;
    }

    public static Type SubstType(Type type, Dictionary<TypeParameter/*!*/,Type/*!*/>/*!*/ subst) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      if (type is BasicType) {
        return type;
      } else if (type is CollectionType) {
        CollectionType t = (CollectionType)type;
        Type arg = SubstType(t.Arg, subst);
        if (arg == t.Arg) {
          return type;
        } else if (type is SetType) {
          return new SetType(arg);
        } else if (type is SeqType) {
          return new SeqType(arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected collection type
        }
      } else if (type is UserDefinedType) {
        UserDefinedType t = (UserDefinedType)type;
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
            return new UserDefinedType(t.tok, t.Name, t.ResolvedClass, newArgs);
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
        } else {
          // bypass the proxy
          return SubstType(t.T, subst);
        }
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
    /// "twoState" implies that "old" and "fresh" expressions are allowed
    /// </summary>
    void ResolveExpression(Expression expr, bool twoState, bool specContext) {
      ResolveExpression(expr, twoState, specContext, null);
    }

    void ResolveExpression(Expression expr, bool twoState, bool specContext, List<IVariable> matchVarContext) {
      Contract.Requires(expr != null);
      Contract.Requires(currentClass != null);
      Contract.Ensures(expr.Type != null);
      if (expr.Type != null) {
        // expression has already been resovled
        return;
      }
      
      // The following cases will resolve the subexpressions and will attempt to assign a type of expr.  However, if errors occur
      // and it cannot be determined what the type of expr is, then it is fine to leave expr.Type as null.  In that case, the end
      // of this method will assign proxy type to the expression, which reduces the number of error messages that are produced
      // while type checking the rest of the program.
      
      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e.Value == null) {
          e.Type = new ObjectTypeProxy();
        } else if (e.Value is BigInteger) {
          e.Type = Type.Int;
        } else if (e.Value is bool) {
          e.Type = Type.Bool;
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
        }
        
      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          Error(expr, "'this' is not allowed in a 'class' context");
        }
        expr.Type = GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
        
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var == null) {
          Error(expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        } else {
          expr.Type = e.Var.Type;
          if (!specContext && e.Var.IsGhost) {
            Error(expr, "ghost variables are allowed only in specification contexts");
          }
        }
      
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        TopLevelDecl d;
        if (!classes.TryGetValue(dtv.DatatypeName, out d)) {
          Error(expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (!(d is DatatypeDecl)) {
          Error(expr.tok, "Expected datatype, found class: {0}", dtv.DatatypeName);
        } else {
          // this resolution is a little special, in that the syntax shows only the base name, not its instantiation (which is inferred)
          DatatypeDecl dt = (DatatypeDecl)d;
          List<Type> gt = new List<Type>(dt.TypeArgs.Count);
          Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
          for (int i = 0; i < dt.TypeArgs.Count; i++) {
            Type t = new InferredTypeProxy();
            gt.Add(t);
            dtv.InferredTypeArgs.Add(t);
            subst.Add(dt.TypeArgs[i], t);
          }
          expr.Type = new UserDefinedType(dtv.tok, dtv.DatatypeName, gt);
          ResolveType(expr.Type);
          
          DatatypeCtor ctor;
          if (!datatypeCtors[dt].TryGetValue(dtv.MemberName, out ctor)) {
            Error(expr.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
          } else {
            Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
            dtv.Ctor = ctor;
            if (ctor.Formals.Count != dtv.Arguments.Count) {
              Error(expr.tok, "wrong number of arguments to datatype constructor {0} (found {1}, expected {2})", dtv.DatatypeName, dtv.Arguments.Count, ctor.Formals.Count);
            }
            // add the constructor's own type parameters to the substitution map
            foreach (TypeParameter p in ctor.TypeArgs) {
              Type t = new ParamTypeProxy(p);
              dtv.InferredTypeArgs.Add(t);
              subst.Add(p, t);
            }
          }
          int j = 0;
          foreach (Expression arg in dtv.Arguments) {
            Formal formal = ctor != null && j < ctor.Formals.Count ? ctor.Formals[j] : null;
            ResolveExpression(arg, twoState, specContext || (formal != null && formal.IsGhost));
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
        
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy();
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, twoState, specContext);
          Contract.Assert(ee.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(elementType, ee.Type)) {
            Error(ee, "All elements of display must be of the same type (got {0}, but type of previous elements is {1})", ee.Type, elementType);
          }
        }
        if (expr is SetDisplayExpr) {
          expr.Type = new SetType(elementType);
        } else {
          expr.Type = new SeqType(elementType);
        }
        
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        ResolveExpression(e.Obj, twoState, specContext);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        UserDefinedType ctype;
        MemberDecl member = ResolveMember(expr.tok, e.Obj.Type, e.FieldName, out ctype);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          Error(expr, "member {0} in class {1} does not refer to a field", e.FieldName, cce.NonNull(ctype).Name);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          e.Field = (Field)member;
          // build the type substitution map
          Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
          for (int i = 0; i < ctype.TypeArgs.Count; i++) {
            subst.Add(ctype.ResolvedClass.TypeArgs[i], ctype.TypeArgs[i]);
          }
          e.Type = SubstType(e.Field.Type, subst);
          if (!specContext && e.Field.IsGhost) {
            Error(expr, "ghost fields are allowed only in specification contexts");
          }
        }
      
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, twoState, specContext, false);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, twoState, specContext);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        if (!UnifyTypes(e.Array.Type, builtIns.ArrayType(e.Indices.Count, elementType))) {
          Error(e.Array, "array selection requires an array (got {0})", e.Array.Type);
        }
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, twoState, specContext);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(idx.Type, Type.Int)) {
            Error(idx, "array selection requires integer indices (got {0} for index {1})", idx.Type, i);
          }
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        bool seqErr = false;
        ResolveExpression(e.Seq, twoState, specContext);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        if (!UnifyTypes(e.Seq.Type, new SeqType(elementType))) {
          Error(expr, "sequence update requires a sequence (got {0})", e.Seq.Type);
          seqErr = true;
        }
        ResolveExpression(e.Index, twoState, specContext);
        Contract.Assert(e.Index.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Index.Type, Type.Int)) {
          Error(e.Index, "sequence update requires integer index (got {0})", e.Index.Type);
        }
        ResolveExpression(e.Value, twoState, specContext);
        Contract.Assert(e.Value.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Value.Type, elementType)) {
          Error(e.Value, "sequence update requires the value to have the element type of the sequence (got {0})", e.Value.Type);
        }
        if (!seqErr) {
          expr.Type = e.Seq.Type;
        }
        
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        ResolveReceiver(e.Receiver, twoState, specContext);
        Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression
        UserDefinedType ctype;
        MemberDecl member = ResolveMember(expr.tok, e.Receiver.Type, e.Name, out ctype);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Function)) {
          Error(expr, "member {0} in class {1} does not refer to a function", e.Name, cce.NonNull(ctype).Name);
        } else {
          Function function = (Function)member;
          e.Function = function;
          if (!specContext && function.IsGhost) {
            Error(expr, "function calls are allowed only in specification contexts (consider declaring the function a 'function method')");
          }
          if (function.Formals.Count != e.Args.Count) {
            Error(expr, "wrong number of function arguments (got {0}, expected {1})", e.Args.Count, function.Formals.Count);
          } else {
            Contract.Assert(ctype != null);  // follows from postcondition of ResolveMember
            if (!scope.AllowInstance && !function.IsStatic && e.Receiver is ThisExpr) {
              // The call really needs an instance, but that instance is given as 'this', which is not
              // available in this context.  In most cases, occurrences of 'this' inside e.Receiver would
              // have been caught in the recursive call to resolve e.Receiver, but not the specific case
              // of e.Receiver being 'this' (explicitly or implicitly), for that case needs to be allowed
              // in the event that a class function calls another class function (and note that we need the
              // type of the receiver in order to find the method, so we could not have made this check
              // earlier).
              Error(e.Receiver, "'this' is not allowed in a 'static' context");
            }
            // build the type substitution map
            Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
            for (int i = 0; i < ctype.TypeArgs.Count; i++) {
              subst.Add(cce.NonNull(ctype.ResolvedClass).TypeArgs[i], ctype.TypeArgs[i]);
            }
            foreach (TypeParameter p in function.TypeArgs) {
              subst.Add(p, new ParamTypeProxy(p));
            }
            // type check the arguments
            for (int i = 0; i < function.Formals.Count; i++) {
              Expression farg = e.Args[i];
              ResolveExpression(farg, twoState, specContext);
              Contract.Assert(farg.Type != null);  // follows from postcondition of ResolveExpression
              Type s = SubstType(function.Formals[i].Type, subst);
              if (!UnifyTypes(farg.Type, s)) {
                Error(expr, "incorrect type of function argument {0} (expected {1}, got {2})", i, s, farg.Type);
              }
            }
            expr.Type = SubstType(function.ResultType, subst);
          }
          
          // Resolution termination check
          if (currentFunction != null && currentFunction.EnclosingClass != null && function.EnclosingClass != null) {
            ModuleDecl callerModule = currentFunction.EnclosingClass.Module;
            ModuleDecl calleeModule = function.EnclosingClass.Module;
            if (callerModule == calleeModule) {
              // intra-module call; this is allowed; add edge in module's call graph
              callerModule.CallGraph.AddEdge(currentFunction, function);
              if (currentFunction == function) {
                currentFunction.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
              }
            } else if (calleeModule.IsDefaultModule) {
              // all is fine: everything implicitly imports the default module
            } else if (importGraph.Reaches(callerModule, calleeModule)) {
              // all is fine: the callee is downstream of the caller
            } else {
              Error(expr, "inter-module calls must follow the module import relation (so module {0} must transitively import {1})", callerModule.Name, calleeModule.Name);
            }
          }
        }
        
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        if (!twoState) {
          Error(expr, "old expressions are not allowed in this context");
        }
        ResolveExpression(e.E, twoState, specContext);
        expr.Type = e.E.Type;
        
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        if (!twoState) {
          Error(expr, "fresh expressions are not allowed in this context");
        }
        ResolveExpression(e.E, twoState, specContext);
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
        } else {
          Error(expr, "the argument of a fresh expression must denote an object or a collection of objects (instead got {0})", e.E.Type);
        }
        expr.Type = Type.Bool;

      } else if (expr is AllocatedExpr) {
        AllocatedExpr e = (AllocatedExpr)expr;
        ResolveExpression(e.E, twoState, specContext);
        // e.E can be of any type
        expr.Type = Type.Bool;

      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        ResolveExpression(e.E, twoState, specContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case UnaryExpr.Opcode.Not:
            if (!UnifyTypes(e.E.Type, Type.Bool)) {
              Error(expr, "logical negation expects a boolean argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Bool;
            break;
          case UnaryExpr.Opcode.SeqLength:
            if (!UnifyTypes(e.E.Type, new SeqType(new InferredTypeProxy()))) {
              Error(expr, "length operator expects a sequence argument (instead got {0})", e.E.Type);
            }
            expr.Type = Type.Int;
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }
        
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, twoState, specContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, twoState, specContext);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
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
            if (!UnifyTypes(e.E0.Type, e.E1.Type)) {
              Error(expr, "arguments must have the same type (got {0} and {1})", e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;
          
          case BinaryExpr.Opcode.Disjoint:
            if (!UnifyTypes(e.E0.Type, new SetType(new InferredTypeProxy()))) {
              Error(expr, "arguments must be of a set type (got {0})", e.E0.Type);
            }
            if (!UnifyTypes(e.E0.Type, e.E1.Type)) {
              Error(expr, "arguments must have the same type (got {0} and {1})", e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;
          
          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le:
          case BinaryExpr.Opcode.Add:
            {
              if (e.Op == BinaryExpr.Opcode.Lt && e.E0.Type.IsDatatype) {
                if (!UnifyTypes(e.E1.Type, new DatatypeProxy())) {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                if (!specContext) {
                  Error(expr, "rank comparisons are allowed only in specification and ghost contexts");
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(true))) {
                  Error(expr, "arguments to {0} must be int or a collection type (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
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
          case BinaryExpr.Opcode.Ge:
            {
              if (e.Op == BinaryExpr.Opcode.Gt && e.E0.Type.IsDatatype) {
                if (!UnifyTypes(e.E1.Type, new DatatypeProxy())) {
                  Error(expr, "arguments to rank comparison must be datatypes (instead of {0})", e.E1.Type);
                }
                if (!specContext) {
                  Error(expr, "rank comparisons are allowed only in specification and ghost contexts");
                }
                expr.Type = Type.Bool;
              } else {
                bool err = false;
                if (!UnifyTypes(e.E0.Type, new OperationTypeProxy(false))) {
                  Error(expr, "arguments to {0} must be int or a set (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
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
              Error(expr, "second argument to {0} must be a set or sequence of type {1} (instead got {2})", BinaryExpr.OpcodeString(e.Op), e.E0.Type, e.E1.Type);
            }
            expr.Type = Type.Bool;
            break;
            
          case BinaryExpr.Opcode.Div:
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
        e.ResolvedOp = ResolveOp(e.Op, e.E1.Type);
        
      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        scope.PushMarker();
        if (!specContext) {
          Error(expr, "quantifiers are allowed only in specification contexts");
        }
        foreach (BoundVar v in e.BoundVars) {
          if (!scope.Push(v.Name, v)) {
            Error(v, "Duplicate bound-variable name: {0}", v.Name);
          }
          ResolveType(v.Type);
        }
        ResolveExpression(e.Body, twoState, specContext);
        Contract.Assert(e.Body.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.Body.Type, Type.Bool)) {
          Error(expr, "body of quantifier must be of type bool (instead got {0})", e.Body.Type);
        }
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes and triggers (below).
        ResolveAttributes(e.Attributes, twoState);
        ResolveTriggers(e.Trigs, twoState);
        scope.PopMarker();
        expr.Type = Type.Bool;
        
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(new ObjectType());
        
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, twoState, specContext);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, twoState, specContext);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, twoState, specContext);
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
        MatchExpr me = (MatchExpr)expr;
        Contract.Assert(!twoState);  // currently, match expressions are allowed only at the outermost level of function bodies
        ResolveExpression(me.Source, twoState, specContext);
        Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression
        UserDefinedType sourceType = null;
        DatatypeDecl dtd = null;
        Dictionary<TypeParameter,Type> subst = new Dictionary<TypeParameter,Type>();
        if (me.Source.Type.IsDatatype) {
          sourceType = (UserDefinedType)me.Source.Type;
          dtd = cce.NonNull((DatatypeDecl)sourceType.ResolvedClass);
        }
        Dictionary<string,DatatypeCtor> ctors;
        IVariable goodMatchVariable = null;
        if (dtd == null) {
          Error(me.Source, "the type of the match source expression must be a datatype");
          ctors = null;
        } else {
          Contract.Assert(sourceType != null);  // dtd and sourceType are set together above
          ctors = datatypeCtors[dtd];
          Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage
          
          IdentifierExpr ie = me.Source as IdentifierExpr;
          if (ie == null || !(ie.Var is Formal || ie.Var is BoundVar)) {
            Error(me.Source.tok, "match source expression must be a formal parameter of the enclosing function or an enclosing match expression");
          } else if (!matchVarContext.Contains(ie.Var)) {
            Error(me.Source.tok, "match source expression '{0}' has already been used as a match source expression in this context", ie.Var.Name);
          } else {
            goodMatchVariable = ie.Var;
          }
          
          // build the type-parameter substitution map for this use of the datatype
          for (int i = 0; i < dtd.TypeArgs.Count; i++) {
            subst.Add(dtd.TypeArgs[i], sourceType.TypeArgs[i]);
          }
        }
        
        Dictionary<string,object> memberNamesUsed = new Dictionary<string,object>();  // this is really a set
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
              if (memberNamesUsed.ContainsKey(mc.Id)) {
                Error(mc.tok, "member {0} appears in more than one case", mc.Id);
              } else {
                memberNamesUsed.Add(mc.Id, null);  // add mc.Id to the set of names used
              }
            }
          }
          scope.PushMarker();
          if (ctor != null) {
            // add the constructor's own type parameters to the substitution map
            foreach (TypeParameter p in ctor.TypeArgs) {
              subst.Add(p, new ParamTypeProxy(p));
            }
          }
          int i = 0;
          foreach (BoundVar v in mc.Arguments) {
            if (!scope.Push(v.Name, v)) {
              Error(v, "Duplicate parameter name: {0}", v.Name);
            }
            ResolveType(v.Type);
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
          List<IVariable> innerMatchVarContext = new List<IVariable>(matchVarContext);
          if (goodMatchVariable != null) {
            innerMatchVarContext.Remove(goodMatchVariable);  // this variable is no longer available for matching
          }
          innerMatchVarContext.AddRange(mc.Arguments);
          ResolveExpression(mc.Body, twoState, specContext, innerMatchVarContext);
          Contract.Assert(mc.Body.Type != null);  // follows from postcondition of ResolveExpression
          if (!UnifyTypes(expr.Type, mc.Body.Type)) {
            Error(mc.Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", mc.Body.Type, expr.Type);
          }
          scope.PopMarker();
        }
        if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
          Error(expr, "match expression does not cover all constructors");
        }
        
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = Type.Flexible;
      }
    }
    
    void ResolveReceiver(Expression expr, bool twoState, bool specContext)
    {
      Contract.Requires(expr != null);
      Contract.Requires(currentClass != null);
      Contract.Ensures(expr.Type != null);
    
      if (expr is ThisExpr) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, twoState, specContext);
      }
    }
    
    void ResolveSeqSelectExpr(SeqSelectExpr e, bool twoState, bool specContext, bool allowNonUnitArraySelection) {
      Contract.Requires(e != null);
      bool seqErr = false;
      ResolveExpression(e.Seq, twoState, specContext);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
      Type elementType = new InferredTypeProxy();
      Type expectedType;
      if (e.SelectOne || allowNonUnitArraySelection) {
        expectedType = new IndexableTypeProxy(elementType);
      } else {
        expectedType = new SeqType(elementType);
      }
      if (!UnifyTypes(e.Seq.Type, expectedType)) {
        Error(e, "sequence/array selection requires a sequence or array (got {0})", e.Seq.Type);
        seqErr = true;
      }
      if (e.E0 != null) {
        ResolveExpression(e.E0, twoState, specContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E0.Type, Type.Int)) {
          Error(e.E0, "sequence/array selection requires integer indices (got {0})", e.E0.Type);
        }
      }
      if (e.E1 != null) {
        ResolveExpression(e.E1, twoState, specContext);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        if (!UnifyTypes(e.E1.Type, Type.Int)) {
          Error(e.E1, "sequence/array selection requires integer indices (got {0})", e.E1.Type);
        }
      }
      if (!seqErr) {
        if (e.SelectOne) {
          e.Type = elementType;
        } else {
          e.Type = e.Seq.Type;
        }
      }
    }
    
    /// <summary>
    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// </summary>
    BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, Type operandType) {
      Contract.Requires(operandType != null);
      switch (op) {
        case BinaryExpr.Opcode.Iff:  return BinaryExpr.ResolvedOpcode.Iff;
        case BinaryExpr.Opcode.Imp:  return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.And:  return BinaryExpr.ResolvedOpcode.And;
        case BinaryExpr.Opcode.Or:  return BinaryExpr.ResolvedOpcode.Or;
        case BinaryExpr.Opcode.Eq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetEq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqEq;
          } else {
            return BinaryExpr.ResolvedOpcode.EqCommon;
          }
        case BinaryExpr.Opcode.Neq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetNeq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqNeq;
          } else {
            return BinaryExpr.ResolvedOpcode.NeqCommon;
          }
        case BinaryExpr.Opcode.Disjoint:  return BinaryExpr.ResolvedOpcode.Disjoint;
        case BinaryExpr.Opcode.Lt:
          if (operandType.IsDatatype) {
            return BinaryExpr.ResolvedOpcode.RankLt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSubset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.ProperPrefix;
          } else {
            return BinaryExpr.ResolvedOpcode.Lt;
          }
        case BinaryExpr.Opcode.Le:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Subset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Prefix;
          } else {
            return BinaryExpr.ResolvedOpcode.Le;
          }
        case BinaryExpr.Opcode.Add:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Union;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Concat;
          } else {
            return BinaryExpr.ResolvedOpcode.Add;
          }
        case BinaryExpr.Opcode.Sub:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetDifference;
          } else {
            return BinaryExpr.ResolvedOpcode.Sub;
          }
        case BinaryExpr.Opcode.Mul:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Intersection;
          } else {
            return BinaryExpr.ResolvedOpcode.Mul;
          }
        case BinaryExpr.Opcode.Gt:
          if (operandType.IsDatatype) {
            return BinaryExpr.ResolvedOpcode.RankGt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSuperset;
          } else {
            return BinaryExpr.ResolvedOpcode.Gt;
          }
        case BinaryExpr.Opcode.Ge:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Superset;
          } else {
            return BinaryExpr.ResolvedOpcode.Ge;
          }
        case BinaryExpr.Opcode.In:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.InSet;
          } else {
            return BinaryExpr.ResolvedOpcode.InSeq;
          }
        case BinaryExpr.Opcode.NotIn:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.NotInSet;
          } else {
            return BinaryExpr.ResolvedOpcode.NotInSeq;
          }
        case BinaryExpr.Opcode.Div:  return BinaryExpr.ResolvedOpcode.Div;
        case BinaryExpr.Opcode.Mod:  return BinaryExpr.ResolvedOpcode.Mod;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
      }
    }

    /// <summary>
    /// Returns whether or not 'expr' has any subexpression that uses some feature (like a ghost or quantifier)
    /// that is allowed only in specification contexts.
    /// Requires 'expr' to be a successfully resolved expression.
    /// </summary>
    bool UsesSpecFeatures(Expression expr)
    {
      Contract.Requires(expr != null);
      Contract.Requires(currentClass != null);
    
      if (expr is LiteralExpr) {
        return false;
      } else if (expr is ThisExpr) {
        return false;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return cce.NonNull(e.Var).IsGhost;
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        return Contract.Exists(dtv.Arguments, arg=> UsesSpecFeatures(arg));
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return Contract.Exists( e.Elements,ee=> UsesSpecFeatures(ee));
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        return cce.NonNull(e.Field).IsGhost || UsesSpecFeatures(e.Obj);
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               (e.E0 != null && UsesSpecFeatures(e.E0)) ||
               (e.E1 != null && UsesSpecFeatures(e.E1));
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
        return Contract.Exists( e.Args,arg=> UsesSpecFeatures(arg));
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is FreshExpr) {
        return true;
      } else if (expr is AllocatedExpr) {
        return true;
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.RankLt || e.ResolvedOp == BinaryExpr.ResolvedOpcode.RankGt) {
          return true;
        }
        return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1);
      } else if (expr is QuantifierExpr) {
        return true;
      } else if (expr is WildcardExpr) {
        return false;
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        return UsesSpecFeatures(e.Test) || UsesSpecFeatures(e.Thn) || UsesSpecFeatures(e.Els);
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        if (UsesSpecFeatures(me.Source)) {
          return true;
        }
        return Contract.Exists( me.Cases,mc=> UsesSpecFeatures(mc.Body));
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }
  }

  class Scope<Thing> where Thing : class {
    [Rep] readonly List<string> names = new List<string>();  // a null means a marker
    [Rep] readonly List<Thing> things = new List<Thing>();
    [ContractInvariantMethod]
    void ObjectInvariant() 
    {
        Contract.Invariant(names != null);
    Contract.Invariant(things != null);
      Contract.Invariant(names.Count == things.Count);
      Contract.Invariant(-1 <= scopeSizeWhereInstancesWereDisallowed && scopeSizeWhereInstancesWereDisallowed <= names.Count);
    }

    int scopeSizeWhereInstancesWereDisallowed = -1;
    
    public bool AllowInstance {
      get { return scopeSizeWhereInstancesWereDisallowed == -1; }
      set
      {Contract.Requires(AllowInstance && !value);  // only allowed to change from true to false (that's all that's currently needed in Dafny); Pop is what can make the change in the other direction
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
    
    // Pushes name-->var association and returns "true", if name has not already been pushed since the last marker.
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
            return null;  // no present
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
  }
}
