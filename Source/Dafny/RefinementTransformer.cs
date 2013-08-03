//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
// This file contains the transformations that are applied to a module that is
// constructed as a refinement of another.  It is invoked during program resolution,
// so the transformation is done syntactically.  Upon return from the RefinementTransformer,
// the caller is expected to resolve the resulting module.
//
// As for now (and perhaps this is always the right thing to do), attributes do
// not survive the transformation.
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny
{
  public class RefinementToken : TokenWrapper
  {
    public readonly ModuleDefinition InheritingModule;
    public RefinementToken(IToken tok, ModuleDefinition m)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(m != null);
      this.InheritingModule = m;
    }

    public static bool IsInherited(IToken tok, ModuleDefinition m) {
      while (tok is NestedToken) {
        var n = (NestedToken)tok;
        // check Outer
        var r = n.Outer as RefinementToken;
        if (r == null || r.InheritingModule != m) {
          return false;
        }
        // continue to check Inner
        tok = n.Inner;
      }
      var rtok = tok as RefinementToken;
      return rtok != null && rtok.InheritingModule == m;
    }
    public override string filename {
      get { return WrappedToken.filename + "[" + InheritingModule.Name + "]"; }
      set { throw new NotSupportedException(); }
    }
  }

  public class RefinementTransformer : IRewriter
  {
    ResolutionErrorReporter reporter;
    Cloner rawCloner; // This cloner just gives exactly the same thing back.
    RefinementCloner refinementCloner; // This cloner wraps things in a RefinementTransformer
    Program program;
    public RefinementTransformer(ResolutionErrorReporter reporter, Program p) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
      rawCloner = new Cloner();
      program = p;
    }

    private ModuleDefinition moduleUnderConstruction;  // non-null for the duration of Construct calls
    private Queue<Action> postTasks = new Queue<Action>();  // empty whenever moduleUnderConstruction==null, these tasks are for the post-resolve phase of module moduleUnderConstruction
    public Queue<Tuple<Method, Method>> translationMethodChecks = new Queue<Tuple<Method, Method>>();  // contains all the methods that need to be checked for structural refinement.
    private Method currentMethod;

    public void PreResolve(ModuleDefinition m) {

      if (m.RefinementBase == null) return;

      if (moduleUnderConstruction != null) {
        postTasks.Clear();
      }
      moduleUnderConstruction = m;
      refinementCloner = new RefinementCloner(moduleUnderConstruction);
      var prev = m.RefinementBase;

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < m.TopLevelDecls.Count; i++) {
        var d = m.TopLevelDecls[i];
        if (!declaredNames.ContainsKey(d.Name)) {
          declaredNames.Add(d.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var d in prev.TopLevelDecls) {
        int index;
        if (!declaredNames.TryGetValue(d.Name, out index)) {
          m.TopLevelDecls.Add(refinementCloner.CloneDeclaration(d, m));
        } else {
          var nw = m.TopLevelDecls[index];
          if (d is ModuleDecl) {
            if (!(nw is ModuleDecl)) {
              reporter.Error(nw, "a module ({0}) must refine another module", nw.Name);
            } else if (!(d is ModuleFacadeDecl)) {
              reporter.Error(nw, "a module ({0}) can only refine a module facade", nw.Name);
            } else {
              ModuleSignature original = ((ModuleFacadeDecl)d).OriginalSignature;
              ModuleSignature derived = null;
              if (nw is AliasModuleDecl) {
                derived = ((AliasModuleDecl)nw).Signature;
              } else if (nw is ModuleFacadeDecl) {
                derived = ((ModuleFacadeDecl)nw).Signature;
              } else {
                reporter.Error(nw, "a module ({0}) can only be refined by an alias module or a module facade", d.Name);
              }
              if (derived != null) {
                // check that the new module refines the previous declaration
                if (!CheckIsRefinement(derived, original))
                  reporter.Error(nw.tok, "a module ({0}) can only be replaced by a refinement of the original module", d.Name);
              }
            }
          } else if (d is ArbitraryTypeDecl) {
            if (nw is ModuleDecl) {
              reporter.Error(nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              bool dDemandsEqualitySupport = ((ArbitraryTypeDecl)d).MustSupportEquality;
              if (nw is ArbitraryTypeDecl) {
                if (dDemandsEqualitySupport != ((ArbitraryTypeDecl)nw).MustSupportEquality) {
                  reporter.Error(nw, "type declaration '{0}' is not allowed to change the requirement of supporting equality", nw.Name);
                }
              } else if (dDemandsEqualitySupport) {
                if (nw is ClassDecl) {
                  // fine, as long as "nw" does not take any type parameters
                  if (nw.TypeArgs.Count != d.TypeArgs.Count) {
                    reporter.Error(nw, "arbitrary type '{0}' is not allowed to be replaced by a class that takes a different number of type parameters", nw.Name);
                  }
                } else if (nw is CoDatatypeDecl) {
                  reporter.Error(nw, "a type declaration that requires equality support cannot be replaced by a codatatype");
                } else {
                  Contract.Assert(nw is IndDatatypeDecl);
                  if (nw.TypeArgs.Count != d.TypeArgs.Count) {
                    reporter.Error(nw, "arbitrary type '{0}' is not allowed to be replaced by a datatype that takes a different number of type parameters", nw.Name);
                  } else {
                    // Here, we need to figure out if the new type supports equality.  But we won't know about that until resolution has
                    // taken place, so we defer it until the PostResolve phase.
                    var udt = new UserDefinedType(nw.tok, nw.Name, nw, new List<Type>());
                    postTasks.Enqueue(delegate() {
                      if (!udt.SupportsEquality) {
                        reporter.Error(udt.tok, "datatype '{0}' is used to refine an arbitrary type with equality support, but '{0}' does not support equality", udt.Name);
                      }
                    });
                  }
                }
              } else if (d.TypeArgs.Count != nw.TypeArgs.Count) {
                reporter.Error(nw, "arbitrary type '{0}' is not allowed to be replaced by a type that takes a different number of type parameters", nw.Name);
              }
            }
          } else if (nw is ArbitraryTypeDecl) {
            reporter.Error(nw, "an arbitrary type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
          } else if (nw is DatatypeDecl) {
            reporter.Error(nw, "a datatype declaration ({0}) in a refinement module can only replace an arbitrary-type declaration", nw.Name);
          } else if (nw is IteratorDecl) {
            if (d is IteratorDecl) {
              m.TopLevelDecls[index] = MergeIterator((IteratorDecl)nw, (IteratorDecl)d);
            } else {
              reporter.Error(nw, "an iterator declaration ({0}) is a refining module cannot replace a different kind of declaration in the refinement base", nw.Name);
            }
          } else {
            Contract.Assert(nw is ClassDecl);
            if (d is DatatypeDecl) {
              reporter.Error(nw, "a class declaration ({0}) in a refining module cannot replace a different kind of declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeClass((ClassDecl)nw, (ClassDecl)d);
            }
          }
        }
      }

      Contract.Assert(moduleUnderConstruction == m);  // this should be as it was set earlier in this method
    }

    public bool CheckIsRefinement(ModuleSignature derived, ModuleSignature original) {
      // Check refinement by construction.
      var derivedPointer = derived;
      while (derivedPointer != null) {
        if (derivedPointer == original)
          return true;
        derivedPointer = derivedPointer.Refines;
      }
      // Check structural refinement. Note this involves several checks.
      // First, we need to know if the two modules are signature compatible;
      // this is determined immediately as it is necessary for determining
      // whether resolution will succeed. This involves checking classes, datatypes,
      // type declarations, and nested modules. 
      // Second, we need to determine whether the specifications will be compatible
      // (i.e. substitutable), by translating to Boogie.

      var errorCount = reporter.ErrorCount;
      foreach (var kv in original.TopLevels) {
        var d = kv.Value;
        TopLevelDecl nw;
        if (derived.TopLevels.TryGetValue(kv.Key, out nw)) {
          if (d is ModuleDecl) {
            if (!(nw is ModuleDecl)) {
              reporter.Error(nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              CheckIsRefinement(((ModuleDecl)nw).Signature, ((ModuleDecl)d).Signature);
            }
          } else if (d is ArbitraryTypeDecl) {
            if (nw is ModuleDecl) {
              reporter.Error(nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              bool dDemandsEqualitySupport = ((ArbitraryTypeDecl)d).MustSupportEquality;
              if (nw is ArbitraryTypeDecl) {
                if (dDemandsEqualitySupport != ((ArbitraryTypeDecl)nw).MustSupportEquality) {
                  reporter.Error(nw, "type declaration '{0}' is not allowed to change the requirement of supporting equality", nw.Name);
                }
              } else if (dDemandsEqualitySupport) {
                if (nw is ClassDecl) {
                  // fine, as long as "nw" does not take any type parameters
                  if (nw.TypeArgs.Count != 0) {
                    reporter.Error(nw, "arbitrary type '{0}' is not allowed to be replaced by a class that takes type parameters", nw.Name);
                  }
                } else if (nw is CoDatatypeDecl) {
                  reporter.Error(nw, "a type declaration that requires equality support cannot be replaced by a codatatype");
                } else {
                  Contract.Assert(nw is IndDatatypeDecl);
                  if (nw.TypeArgs.Count != 0) {
                    reporter.Error(nw, "arbitrary type '{0}' is not allowed to be replaced by a datatype that takes type parameters", nw.Name);
                  } else {
                    var udt = new UserDefinedType(nw.tok, nw.Name, nw, new List<Type>());
                    if (!(udt.SupportsEquality)) {
                      reporter.Error(nw.tok, "datatype '{0}' is used to refine an arbitrary type with equality support, but '{0}' does not support equality", nw.Name);
                    }
                  }
                }
              }
            }
          } else if (d is DatatypeDecl) {
            if (nw is DatatypeDecl) {
              if (d is IndDatatypeDecl && !(nw is IndDatatypeDecl)) {
                reporter.Error(nw, "a datatype ({0}) must be replaced by a datatype, not a codatatype", d.Name);
              } else if (d is CoDatatypeDecl && !(nw is CoDatatypeDecl)) {
                reporter.Error(nw, "a codatatype ({0}) must be replaced by a codatatype, not a datatype", d.Name);
              }
              // check constructors, formals, etc.
              CheckDatatypesAreRefinements((DatatypeDecl)d, (DatatypeDecl)nw);
            } else {
              reporter.Error(nw, "a {0} ({1}) must be refined by a {0}", d is IndDatatypeDecl ? "datatype" : "codatatype", d.Name);
            }
          } else if (d is ClassDecl) {
            if (!(nw is ClassDecl)) {
              reporter.Error(nw, "a class declaration ({0}) must be refined by another class declaration", nw.Name);
            } else {
              CheckClassesAreRefinements((ClassDecl)nw, (ClassDecl)d);
            }
          } else {
            Contract.Assert(false); throw new cce.UnreachableException(); // unexpected toplevel
          }
        } else {
          reporter.Error(d, "declaration {0} must have a matching declaration in the refining module", d.Name);
        }
      }
      return errorCount == reporter.ErrorCount;
    }

    private void CheckClassesAreRefinements(ClassDecl nw, ClassDecl d) {
      if (nw.TypeArgs.Count != d.TypeArgs.Count) {
        reporter.Error(nw, "a refining class ({0}) must have the same number of type parameters", nw.Name);
      } else {
        var map = new Dictionary<string, MemberDecl>();
        foreach (var mem in nw.Members) {
          map.Add(mem.Name, mem);
        }
        foreach (var m in d.Members) {
          MemberDecl newMem;
          if (map.TryGetValue(m.Name, out newMem)) {
            if (m.IsStatic != newMem.IsStatic) {
              reporter.Error(newMem, "member {0} must {1}", m.Name, m.IsStatic? "be static" : "not be static");
            }
            if (m is Field) {
              if (newMem is Field) {
                var newField = (Field)newMem;
                if (!ResolvedTypesAreTheSame(newField.Type, ((Field)m).Type))
                  reporter.Error(newMem, "field must be refined by a field with the same type (got {0}, expected {1})", newField.Type, ((Field)m).Type);
                if (m.IsGhost || !newField.IsGhost)
                  reporter.Error(newField, "a field re-declaration ({0}) must be to ghostify the field", newField.Name, nw.Name);
              } else {
                reporter.Error(newMem, "a field declaration ({1}) must be replaced by a field in the refinement base (not {0})", newMem.Name, nw.Name);
              }
            } else if (m is Method) {
              if (newMem is Method) {
                CheckMethodsAreRefinements((Method)newMem, (Method)m);
              } else {
                reporter.Error(newMem, "method must be refined by a method");
              }
            } else if (m is Function) {
              if (newMem is Function) {
                CheckFunctionsAreRefinements((Function)newMem, (Function)m);
              } else {
                bool isPredicate = m is Predicate;
                bool isCoPredicate = m is CoPredicate;
                string s = isPredicate ? "predicate" : isCoPredicate ? "copredicate" : "function";
                reporter.Error(newMem, "{0} must be refined by a {0}", s);
              }
            }
          } else {
            reporter.Error(nw is DefaultClassDecl ? nw.Module.tok : nw.tok, "refining {0} must have member {1}", nw is DefaultClassDecl ? "module" : "class", m.Name);
          }
        }
      }
    }
    void CheckAgreementResolvedParameters(IToken tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(parameterKind != null);
      if (old.Count != nw.Count) {
        reporter.Error(tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (!o.IsGhost && n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!ResolvedTypesAreTheSame(o.Type, n.Type)) {
            reporter.Error(n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
          }
        }
      }
    }
    private void CheckMethodsAreRefinements(Method nw, Method m) {
      CheckAgreement_TypeParameters(nw.tok, m.TypeArgs, nw.TypeArgs, m.Name, "method", false);
      CheckAgreementResolvedParameters(nw.tok, m.Ins, nw.Ins, m.Name, "method", "in-parameter");
      CheckAgreementResolvedParameters(nw.tok, m.Outs, nw.Outs, m.Name, "method", "out-parameter");
      program.TranslationTasks.Add(new MethodCheck(nw, m));
    }
    private void CheckFunctionsAreRefinements(Function nw, Function f) {
      if (f is Predicate) {
        if (!(nw is Predicate)) {
          reporter.Error(nw, "a predicate declaration ({0}) can only be refined by a predicate", nw.Name);
        } else {
          CheckAgreement_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "predicate", false);
          CheckAgreementResolvedParameters(nw.tok, f.Formals, nw.Formals, nw.Name, "predicate", "parameter");
        }
      } else if (f is CoPredicate) {
        reporter.Error(nw, "refinement of co-predicates is not supported");
      } else {
        // f is a plain Function
        if (nw is Predicate || nw is CoPredicate) {
          reporter.Error(nw, "a {0} declaration ({1}) can only be refined by a function or function method", nw.IsGhost ? "function" : "function method", nw.Name);
        } else {
          CheckAgreement_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "function", false);
          CheckAgreementResolvedParameters(nw.tok, f.Formals, nw.Formals, nw.Name, "function", "parameter");
          if (!ResolvedTypesAreTheSame(nw.ResultType, f.ResultType)) {
            reporter.Error(nw, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", nw.Name, nw.ResultType, f.ResultType);
          }
        }
      }
      program.TranslationTasks.Add(new FunctionCheck(nw, f));
    }


    private void CheckDatatypesAreRefinements(DatatypeDecl dd, DatatypeDecl nn) {
      CheckAgreement_TypeParameters(nn.tok, dd.TypeArgs, nn.TypeArgs, dd.Name, "datatype", false);
      if (dd.Ctors.Count != nn.Ctors.Count) {
        reporter.Error(nn.tok, "a refining datatype must have the same number of constructors");
      } else {
        var map = new Dictionary<string, DatatypeCtor>();
        foreach (var ctor in nn.Ctors) {
          map.Add(ctor.Name, ctor);
        }
        foreach (var ctor in dd.Ctors) {
          DatatypeCtor newCtor;
          if (map.TryGetValue(ctor.Name, out newCtor)) {
            if (newCtor.Formals.Count != ctor.Formals.Count) {
              reporter.Error(newCtor, "the constructor ({0}) must have the same number of formals as in the refined module", newCtor.Name); 
            } else {
              for (int i = 0; i < newCtor.Formals.Count; i++) {
                var a = ctor.Formals[i]; var b = newCtor.Formals[i];
                if (a.HasName) {
                  if (!b.HasName || a.Name != b.Name)
                    reporter.Error(b, "formal argument {0} in constructor {1} does not have the same name as in the refined module (should be {2})", i, ctor.Name, a.Name);
                }
                if (!ResolvedTypesAreTheSame(a.Type, b.Type)) {
                  reporter.Error(b, "formal argument {0} in constructor {1} does not have the same type as in the refined module (should be {2}, not {3})", i, ctor.Name, a.Type.ToString(), b.Type.ToString());
                }
              }
            }
          } else {
            reporter.Error(nn, "the constructor {0} must be present in the refining datatype", ctor.Name);
          }
        }
      }
      
    }
    // Check that two resolved types are the same in a similar context (the same type parameters, method, class, etc.)
    // Assumes that prev is in a previous refinement, and next is in some refinement. Note this is not communative.
    public static bool ResolvedTypesAreTheSame(Type prev, Type next) {
      Contract.Requires(prev != null);
      Contract.Requires(next != null);
      if (prev is TypeProxy || next is TypeProxy)
        return false;

      if (prev is BoolType) {
        return next is BoolType;
      } else if (prev is IntType) {
        if (next is IntType) {
          return (prev is NatType) == (next is NatType);
        } else return false;
      } else if (prev is ObjectType) {
        return next is ObjectType;
      } else if (prev is SetType) {
        return next is SetType && ResolvedTypesAreTheSame(((SetType)prev).Arg, ((SetType)next).Arg);
      } else if (prev is MultiSetType) {
        return next is MultiSetType && ResolvedTypesAreTheSame(((MultiSetType)prev).Arg, ((MultiSetType)next).Arg);
      } else if (prev is MapType) {
        return next is MapType && ResolvedTypesAreTheSame(((MapType)prev).Domain, ((MapType)next).Domain) && ResolvedTypesAreTheSame(((MapType)prev).Range, ((MapType)next).Range);
      } else if (prev is SeqType) {
        return next is SeqType && ResolvedTypesAreTheSame(((SeqType)prev).Arg, ((SeqType)next).Arg);
      } else if (prev is UserDefinedType) {
        if (!(next is UserDefinedType)) {
          return false;
        }
        UserDefinedType aa = (UserDefinedType)prev;
        UserDefinedType bb = (UserDefinedType)next;
        if (aa.ResolvedClass != null && aa.ResolvedClass.Name == bb.ResolvedClass.Name) {
          // these are both resolved class/datatype types
          Contract.Assert(aa.TypeArgs.Count == bb.TypeArgs.Count);
          for (int i = 0; i < aa.TypeArgs.Count; i++)
            if (!ResolvedTypesAreTheSame(aa.TypeArgs[i], bb.TypeArgs[i]))
              return false;
          return true;
        } else if (aa.ResolvedParam != null && bb.ResolvedParam != null) {
          // these are both resolved type parameters
          Contract.Assert(aa.TypeArgs.Count == 0 && bb.TypeArgs.Count == 0);
          // Note that this is only correct if the two types occur in the same context, ie. both from the same method
          // or class field.
          return aa.ResolvedParam.PositionalIndex == bb.ResolvedParam.PositionalIndex &&
                 aa.ResolvedParam.IsToplevelScope == bb.ResolvedParam.IsToplevelScope;
        } else if (aa.ResolvedParam.IsAbstractTypeDeclaration && bb.ResolvedClass != null) {
          return (aa.ResolvedParam.Name == bb.ResolvedClass.Name);
        } else {
          // something is wrong; either aa or bb wasn't properly resolved, or they aren't the same
          return false;
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }
    public void PostResolve(ModuleDefinition m) {
      if (m == moduleUnderConstruction) {
        while (this.postTasks.Count != 0) {
          var a = postTasks.Dequeue();
          a();
        }
      } else {
        postTasks.Clear();
      }
      moduleUnderConstruction = null;
    }
    Function CloneFunction(IToken tok, Function f, bool isGhost, List<Expression> moreEnsures, Expression moreBody, Expression replacementBody, bool checkPrevPostconditions, Attributes moreAttributes) {
      Contract.Requires(tok != null);
      Contract.Requires(moreBody == null || f is Predicate);
      Contract.Requires(moreBody == null || replacementBody == null);

      var tps = f.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam);
      var formals = f.Formals.ConvertAll(refinementCloner.CloneFormal);
      var req = f.Req.ConvertAll(refinementCloner.CloneExpr);
      var reads = f.Reads.ConvertAll(refinementCloner.CloneFrameExpr);
      var decreases = refinementCloner.CloneSpecExpr(f.Decreases);

      List<Expression> ens;
      if (checkPrevPostconditions)  // note, if a postcondition includes something that changes in the module, the translator will notice this and still re-check the postcondition
        ens = f.Ens.ConvertAll(rawCloner.CloneExpr);
      else
        ens = f.Ens.ConvertAll(refinementCloner.CloneExpr);
      if (moreEnsures != null) {
        ens.AddRange(moreEnsures);
      }

      Expression body;
      Predicate.BodyOriginKind bodyOrigin;
      if (replacementBody != null) {
        body = replacementBody;
        bodyOrigin = Predicate.BodyOriginKind.DelayedDefinition;
      } else if (moreBody != null) {
        if (f.Body == null) {
          body = moreBody;
          bodyOrigin = Predicate.BodyOriginKind.DelayedDefinition;
        } else {
          body = new BinaryExpr(f.tok, BinaryExpr.Opcode.And, refinementCloner.CloneExpr(f.Body), moreBody);
          bodyOrigin = Predicate.BodyOriginKind.Extension;
        }
      } else {
        body = refinementCloner.CloneExpr(f.Body);
        bodyOrigin = Predicate.BodyOriginKind.OriginalOrInherited;
      }

      if (f is Predicate) {
        return new Predicate(tok, f.Name, f.IsStatic, isGhost, tps, f.OpenParen, formals,
          req, reads, ens, decreases, body, bodyOrigin, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), false);
      } else if (f is CoPredicate) {
        return new CoPredicate(tok, f.Name, f.IsStatic, tps, f.OpenParen, formals,
          req, reads, ens, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), false);
      } else {
        return new Function(tok, f.Name, f.IsStatic, isGhost, tps, f.OpenParen, formals, refinementCloner.CloneType(f.ResultType),
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), false);
      }
    }

    Method CloneMethod(Method m, List<MaybeFreeExpression> moreEnsures, Specification<Expression> decreases, BlockStmt newBody, bool checkPreviousPostconditions, Attributes moreAttributes) {
      Contract.Requires(m != null);
      Contract.Requires(decreases != null);

      var tps = m.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam);
      var ins = m.Ins.ConvertAll(refinementCloner.CloneFormal);
      var req = m.Req.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
      var mod = refinementCloner.CloneSpecFrameExpr(m.Mod);

      List<MaybeFreeExpression> ens;
      if (checkPreviousPostconditions)
        ens = m.Ens.ConvertAll(rawCloner.CloneMayBeFreeExpr);
      else
        ens = m.Ens.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
      if (moreEnsures != null) {
        ens.AddRange(moreEnsures);
      }

      var body = newBody ?? refinementCloner.CloneBlockStmt(m.Body);
      if (m is Constructor) {
        return new Constructor(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, tps, ins,
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), false);
      } else if (m is CoMethod) {
        return new CoMethod(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.IsStatic, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), false);
      } else if (m is Lemma) {
        return new Lemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.IsStatic, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), false);
      } else {
        return new Method(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.IsStatic, m.IsGhost, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), false);
      }
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    IteratorDecl MergeIterator(IteratorDecl nw, IteratorDecl prev) {
      Contract.Requires(nw != null);
      Contract.Requires(prev != null);

      if (nw.Requires.Count != 0) {
        reporter.Error(nw.Requires[0].E.tok, "a refining iterator is not allowed to add preconditions");
      }
      if (nw.YieldRequires.Count != 0) {
        reporter.Error(nw.YieldRequires[0].E.tok, "a refining iterator is not allowed to add yield preconditions");
      }
      if (nw.Reads.Expressions.Count != 0) {
        reporter.Error(nw.Reads.Expressions[0].E.tok, "a refining iterator is not allowed to extend the reads clause");
      }
      if (nw.Modifies.Expressions.Count != 0) {
        reporter.Error(nw.Modifies.Expressions[0].E.tok, "a refining iterator is not allowed to extend the modifies clause");
      }
      if (nw.Decreases.Expressions.Count != 0) {
        reporter.Error(nw.Decreases.Expressions[0].tok, "a refining iterator is not allowed to extend the decreases clause");
      }

      if (nw.SignatureIsOmitted) {
        Contract.Assert(nw.TypeArgs.Count == 0);
        Contract.Assert(nw.Ins.Count == 0);
        Contract.Assert(nw.Outs.Count == 0);
      } else {
        CheckAgreement_TypeParameters(nw.tok, prev.TypeArgs, nw.TypeArgs, nw.Name, "iterator");
        CheckAgreement_Parameters(nw.tok, prev.Ins, nw.Ins, nw.Name, "iterator", "in-parameter");
        CheckAgreement_Parameters(nw.tok, prev.Outs, nw.Outs, nw.Name, "iterator", "yield-parameter");
      }

      BlockStmt newBody;
      if (nw.Body == null) {
        newBody = prev.Body;
      } else if (prev.Body == null) {
        newBody = nw.Body;
      } else {
        newBody = MergeBlockStmt(nw.Body, prev.Body);
      }

      var ens = prev.Ensures.ConvertAll(rawCloner.CloneMayBeFreeExpr);
      ens.AddRange(nw.Ensures);
      var yens = prev.YieldEnsures.ConvertAll(rawCloner.CloneMayBeFreeExpr);
      yens.AddRange(nw.YieldEnsures);

      return new IteratorDecl(new RefinementToken(nw.tok, moduleUnderConstruction), nw.Name, moduleUnderConstruction,
        nw.SignatureIsOmitted ? prev.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam) : nw.TypeArgs,
        nw.SignatureIsOmitted ? prev.Ins.ConvertAll(refinementCloner.CloneFormal) : nw.Ins,
        nw.SignatureIsOmitted ? prev.Outs.ConvertAll(refinementCloner.CloneFormal) : nw.Outs,
        refinementCloner.CloneSpecFrameExpr(prev.Reads),
        refinementCloner.CloneSpecFrameExpr(prev.Modifies),
        refinementCloner.CloneSpecExpr(prev.Decreases),
        prev.Requires.ConvertAll(refinementCloner.CloneMayBeFreeExpr),
        ens,
        prev.YieldRequires.ConvertAll(refinementCloner.CloneMayBeFreeExpr),
        yens,
        newBody,
        refinementCloner.MergeAttributes(prev.Attributes, nw.Attributes),
        false);
    }

    ClassDecl MergeClass(ClassDecl nw, ClassDecl prev) {
      CheckAgreement_TypeParameters(nw.tok, prev.TypeArgs, nw.TypeArgs, nw.Name, "class");

      nw.Attributes = refinementCloner.MergeAttributes(prev.Attributes, nw.Attributes);

      // Create a simple name-to-member dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < nw.Members.Count; i++) {
        var member = nw.Members[i];
        if (!declaredNames.ContainsKey(member.Name)) {
          declaredNames.Add(member.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var member in prev.Members) {
        int index;
        if (!declaredNames.TryGetValue(member.Name, out index)) {
          var nwMember = refinementCloner.CloneMember(member);
          nwMember.RefinementBase = member;
          nw.Members.Add(nwMember);
        } else {
          var nwMember = nw.Members[index];
          if (nwMember is Field) {
            if (member is Field && TypesAreSyntacticallyEqual(((Field)nwMember).Type, ((Field)member).Type)) {
              if (member.IsGhost || !nwMember.IsGhost)
                reporter.Error(nwMember, "a field re-declaration ({0}) must be to ghostify the field", nwMember.Name, nw.Name);
            } else {
              reporter.Error(nwMember, "a field declaration ({0}) in a refining class ({1}) must replace a field in the refinement base", nwMember.Name, nw.Name);
            }
            nwMember.RefinementBase = member;

          } else if (nwMember is Function) {
            var f = (Function)nwMember;
            bool isPredicate = f is Predicate;
            bool isCoPredicate = f is CoPredicate;
            string s = isPredicate ? "predicate" : isCoPredicate ? "copredicate" : "function";
            if (!(member is Function) || (isPredicate && !(member is Predicate)) || (isCoPredicate && !(member is CoPredicate))) {
              reporter.Error(nwMember, "a {0} declaration ({1}) can only refine a {0}", s, nwMember.Name);
            } else {
              var prevFunction = (Function)member;
              if (f.Req.Count != 0) {
                reporter.Error(f.Req[0].tok, "a refining {0} is not allowed to add preconditions", s);
              }
              if (f.Reads.Count != 0) {
                reporter.Error(f.Reads[0].E.tok, "a refining {0} is not allowed to extend the reads clause", s);
              }
              if (f.Decreases.Expressions.Count != 0) {
                reporter.Error(f.Decreases.Expressions[0].tok, "decreases clause on refining {0} not supported", s);
              }

              if (prevFunction.IsStatic != f.IsStatic) {
                reporter.Error(f, "a function in a refining module cannot be changed from static to non-static or vice versa: {0}", f.Name);
              }
              if (!prevFunction.IsGhost && f.IsGhost) {
                reporter.Error(f, "a function method cannot be changed into a (ghost) function in a refining module: {0}", f.Name);
              } else if (prevFunction.IsGhost && !f.IsGhost && prevFunction.Body != null) {
                reporter.Error(f, "a function can be changed into a function method in a refining module only if the function has not yet been given a body: {0}", f.Name);
              }
              if (f.SignatureIsOmitted) {
                Contract.Assert(f.TypeArgs.Count == 0);
                Contract.Assert(f.Formals.Count == 0);
              } else {
                CheckAgreement_TypeParameters(f.tok, prevFunction.TypeArgs, f.TypeArgs, f.Name, "function");
                CheckAgreement_Parameters(f.tok, prevFunction.Formals, f.Formals, f.Name, "function", "parameter");
                if (!TypesAreSyntacticallyEqual(prevFunction.ResultType, f.ResultType)) {
                  reporter.Error(f, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", f.Name, f.ResultType, prevFunction.ResultType);
                }
              }

              Expression moreBody = null;
              Expression replacementBody = null;
              if (prevFunction.Body == null) {
                replacementBody = f.Body;
              } else if (isPredicate) {
                moreBody = f.Body;
              } else if (f.Body != null) {
                reporter.Error(nwMember, "a refining function is not allowed to extend/change the body");
              }
              var newF = CloneFunction(f.tok, prevFunction, f.IsGhost, f.Ens, moreBody, replacementBody, prevFunction.Body == null, f.Attributes);
              newF.RefinementBase = member;
              nw.Members[index] = newF;
            }

          } else {
            var m = (Method)nwMember;
            if (!(member is Method)) {
              reporter.Error(nwMember, "a method declaration ({0}) can only refine a method", nwMember.Name);
            } else {
              var prevMethod = (Method)member;
              if (m.Req.Count != 0) {
                reporter.Error(m.Req[0].E.tok, "a refining method is not allowed to add preconditions");
              }
              if (m.Mod.Expressions.Count != 0) {
                reporter.Error(m.Mod.Expressions[0].E.tok, "a refining method is not allowed to extend the modifies clause");
              }
              Specification<Expression> decreases;
              if (Contract.Exists(prevMethod.Decreases.Expressions, e => e is WildcardExpr)) {
                decreases = m.Decreases;
              } else {
                if (m.Decreases.Expressions.Count != 0) {
                  reporter.Error(m.Decreases.Expressions[0].tok, "decreases clause on refining method not supported, unless the refined method was specified with 'decreases *'");
                }
                decreases = refinementCloner.CloneSpecExpr(prevMethod.Decreases);
              }
              if (prevMethod.IsStatic != m.IsStatic) {
                reporter.Error(m, "a method in a refining module cannot be changed from static to non-static or vice versa: {0}", m.Name);
              }
              if (prevMethod.IsGhost && !m.IsGhost) {
                reporter.Error(m, "a method cannot be changed into a ghost method in a refining module: {0}", m.Name);
              } else if (!prevMethod.IsGhost && m.IsGhost) {
                reporter.Error(m, "a ghost method cannot be changed into a non-ghost method in a refining module: {0}", m.Name);
              }
              if (m.SignatureIsOmitted) {
                Contract.Assert(m.TypeArgs.Count == 0);
                Contract.Assert(m.Ins.Count == 0);
                Contract.Assert(m.Outs.Count == 0);
              } else {
                CheckAgreement_TypeParameters(m.tok, prevMethod.TypeArgs, m.TypeArgs, m.Name, "method");
                CheckAgreement_Parameters(m.tok, prevMethod.Ins, m.Ins, m.Name, "method", "in-parameter");
                CheckAgreement_Parameters(m.tok, prevMethod.Outs, m.Outs, m.Name, "method", "out-parameter");
              }
              currentMethod = m;
              var replacementBody = m.Body;
              if (replacementBody != null) {
                if (prevMethod.Body == null) {
                  // cool
                } else {
                  replacementBody = MergeBlockStmt(replacementBody, prevMethod.Body);
                }
              }
              var newM = CloneMethod(prevMethod, m.Ens, decreases, replacementBody, prevMethod.Body == null, m.Attributes);
              newM.RefinementBase = member;
              nw.Members[index] = newM;
            }
          }
        }
      }

      return nw;
    }
    void CheckAgreement_TypeParameters(IToken tok, List<TypeParameter> old, List<TypeParameter> nw, string name, string thing, bool checkNames = true) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      if (old.Count != nw.Count) {
        reporter.Error(tok, "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than the corresponding {0} in the module it refines", thing, name, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name && checkNames) { // if checkNames is false, then just treat the parameters positionally.
            reporter.Error(n.tok, "type parameters are not allowed to be renamed from the names given in the {0} in the module being refined (expected '{1}', found '{2}')", thing, o.Name, n.Name);
          } else {
            // This explains what we want to do and why:
            // switch (o.EqualitySupport) {
            //   case TypeParameter.EqualitySupportValue.Required:
            //     // here, we will insist that the new type-parameter also explicitly requires equality support (because we don't want
            //     // to wait for the inference to run on the new module)
            //     good = n.EqualitySupport == TypeParameter.EqualitySupportValue.Required;
            //     break;
            //   case TypeParameter.EqualitySupportValue.InferredRequired:
            //     // here, we can allow anything, because even with an Unspecified value, the inference will come up with InferredRequired, like before
            //     good = true;
            //     break;
            //   case TypeParameter.EqualitySupportValue.Unspecified:
            //     // inference didn't come up with anything on the previous module, so the only value we'll allow here is Unspecified as well
            //     good = n.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified;
            //     break;
            // }
            // Here's how we actually compute it:
            if (o.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired && o.EqualitySupport != n.EqualitySupport) {
              reporter.Error(n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
            }
          }
        }
      }
    }

    void CheckAgreement_Parameters(IToken tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(parameterKind != null);
      if (old.Count != nw.Count) {
        reporter.Error(tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            reporter.Error(n.tok, "there is a difference in name of {0} {1} ('{2}' versus '{3}') of {4} {5} compared to corresponding {4} in the module it refines", parameterKind, i, n.Name, o.Name, thing, name);
          } else if (!o.IsGhost && n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!TypesAreSyntacticallyEqual(o.Type, n.Type)) {
            reporter.Error(n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
          }
        }
      }
    }

    bool TypesAreSyntacticallyEqual(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      return t.ToString() == u.ToString();
    }

    BlockStmt MergeBlockStmt(BlockStmt skeleton, BlockStmt oldStmt) {
      Contract.Requires(skeleton != null);
      Contract.Requires(oldStmt != null);

      var body = new List<Statement>();
      int i = 0, j = 0;
      while (i < skeleton.Body.Count) {
        var cur = skeleton.Body[i];
        if (j == oldStmt.Body.Count) {
          if (!(cur is SkeletonStatement)) {
            MergeAddStatement(cur, body);
          } else if (((SkeletonStatement)cur).S == null) {
            // the "..." matches the empty statement sequence
          } else {
            reporter.Error(cur.Tok, "skeleton statement does not match old statement");
          }
          i++;
        } else {
          var oldS = oldStmt.Body[j];
          /* See how the two statements match up.
           *   cur                         oldS                         result
           *   ------                      ------                       ------
           *   assert ...;                 assume E;                    assert E;
           *   assert ...;                 assert E;                    assert E;
           *   assert E;                                                assert E;
           *   
           *   assume ...;                 assume E;                    assume E;
           *   
           *   var x := E;                 var x;                       var x := E;
           *   var x := E;                 var x := *;                  var x := E;
           *   var x := E1;                var x :| P;                  var x := E1; assert P;
           *   var VarProduction;                                       var VarProduction;
           *   
           *   x := E;                     x := *;                      x := E;
           *   x := E;                     x :| P;                      x := E; assert P;
           *   
           *   if ... Then else Else       if (G) Then' else Else'      if (G) Merge(Then,Then') else Merge(Else,Else')
           *   if (G) Then else Else       if (*) Then' else Else'      if (G) Merge(Then,Then') else Merge(Else,Else')
           *
           *   while ... LoopSpec ...      while (G) LoopSpec' Body     while (G) Merge(LoopSpec,LoopSpec') Body
           *   while ... LoopSpec Body     while (G) LoopSpec' Body'    while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   while (G) LoopSpec ...      while (*) LoopSpec' Body     while (G) Merge(LoopSpec,LoopSpec') Body
           *   while (G) LoopSpec Body     while (*) LoopSpec' Body'    while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   
           *   ... where x = e; S          StmtThatDoesNotMatchS; S'    StatementThatDoesNotMatchS[e/x]; Merge( ... where x = e; S , S')
           *   ... where x = e; S          StmtThatMatchesS; S'         StmtThatMatchesS; S'
           * 
           * Note, LoopSpec must contain only invariant declarations (as the parser ensures for the first three cases).
           * Note, there is an implicit "...;" at the end of every block in a skeleton.
           */
          if (cur is SkeletonStatement) {
            var S = ((SkeletonStatement)cur).S;
            var c = (SkeletonStatement)cur;
            if (S == null) {
              var nxt = i + 1 == skeleton.Body.Count ? null : skeleton.Body[i + 1];
              if (nxt != null && nxt is SkeletonStatement && ((SkeletonStatement)nxt).S == null) {
                // "...; ...;" is the same as just "...;", so skip this one
              } else {
                SubstitutionCloner subber = null;
                if (c.NameReplacements != null) {
                  var subExprs = new Dictionary<string, Expression>();
                  Contract.Assert(c.NameReplacements.Count == c.ExprReplacements.Count);
                  for (int k = 0; k < c.NameReplacements.Count; k++) {
                    if (subExprs.ContainsKey(c.NameReplacements[k].val)) {
                      reporter.Error(c.NameReplacements[k], "replacement definition must contain at most one definition for a given label");
                    } else subExprs.Add(c.NameReplacements[k].val, c.ExprReplacements[k]);
                  }
                  subber = new SubstitutionCloner(subExprs, rawCloner);
                }
                // skip up until the next thing that matches "nxt"
                while (nxt == null || !PotentialMatch(nxt, oldS)) {
                  // loop invariant:  oldS == oldStmt.Body[j]
                  var s = refinementCloner.CloneStmt(oldS);
                  if (subber != null)
                    s = subber.CloneStmt(s);
                  body.Add(s);
                  j++;
                  if (j == oldStmt.Body.Count) { break; }
                  oldS = oldStmt.Body[j];
                }
                if (subber != null && subber.SubstitutionsMade.Count < subber.Exprs.Count) {
                  foreach (var s in subber.SubstitutionsMade)
                    subber.Exprs.Remove(s);
                  reporter.Error(c.Tok, "could not find labeled expression(s): " + Util.Comma(", ", subber.Exprs.Keys, x => x));
                }
              }
              i++;

            } else if (S is AssertStmt) {
              var skel = (AssertStmt)S;
              Contract.Assert(((SkeletonStatement)cur).ConditionOmitted);
              var oldAssume = oldS as PredicateStmt;
              if (oldAssume == null) {
                reporter.Error(cur.Tok, "assert template does not match inherited statement");
                i++;
              } else {
                // Clone the expression, but among the new assert's attributes, indicate
                // that this assertion is supposed to be translated into a check.  That is,
                // it is not allowed to be just assumed in the translation, despite the fact
                // that the condition is inherited.
                var e = refinementCloner.CloneExpr(oldAssume.Expr);
                var attrs = refinementCloner.MergeAttributes(oldAssume.Attributes, skel.Attributes);
                body.Add(new AssertStmt(new Translator.ForceCheckToken(skel.Tok), e, new Attributes("prependAssertToken", new List<Attributes.Argument>(), attrs)));
                i++; j++;
              }

            } else if (S is AssumeStmt) {
              var skel = (AssumeStmt)S;
              Contract.Assert(((SkeletonStatement)cur).ConditionOmitted);
              var oldAssume = oldS as AssumeStmt;
              if (oldAssume == null) {
                reporter.Error(cur.Tok, "assume template does not match inherited statement");
                i++;
              } else {
                var e = refinementCloner.CloneExpr(oldAssume.Expr);
                var attrs = refinementCloner.MergeAttributes(oldAssume.Attributes, skel.Attributes);
                body.Add(new AssumeStmt(skel.Tok, e, attrs));
                i++; j++;
              }

            } else if (S is IfStmt) {
              var skel = (IfStmt)S;
              Contract.Assert(((SkeletonStatement)cur).ConditionOmitted);
              var oldIf = oldS as IfStmt;
              if (oldIf == null) {
                reporter.Error(cur.Tok, "if-statement template does not match inherited statement");
                i++;
              } else {
                var resultingThen = MergeBlockStmt(skel.Thn, oldIf.Thn);
                var resultingElse = MergeElse(skel.Els, oldIf.Els);
                var r = new IfStmt(skel.Tok, refinementCloner.CloneExpr(oldIf.Guard), resultingThen, resultingElse);
                body.Add(r);
                i++; j++;
              }

            } else if (S is WhileStmt) {
              var skel = (WhileStmt)S;
              var oldWhile = oldS as WhileStmt;
              if (oldWhile == null) {
                reporter.Error(cur.Tok, "while-statement template does not match inherited statement");
                i++;
              } else {
                Expression guard;
                if (((SkeletonStatement)cur).ConditionOmitted) {
                  guard = refinementCloner.CloneExpr(oldWhile.Guard);
                } else {
                  if (oldWhile.Guard != null) {
                    reporter.Error(skel.Guard.tok, "a skeleton while statement with a guard can only replace a while statement with a non-deterministic guard");
                  }
                  guard = skel.Guard;
                }
                // Note, if the loop body is omitted in the skeleton, the parser will have set the loop body to an empty block,
                // which has the same merging behavior.
                var r = MergeWhileStmt(skel, oldWhile, guard);
                body.Add(r);
                i++; j++;
              }

            } else {
              Contract.Assume(false);  // unexpected skeleton statement
            }

          } else if (cur is AssertStmt) {
            MergeAddStatement(cur, body);
            i++;

          } else if (cur is VarDeclStmt) {
            var cNew = (VarDeclStmt)cur;
            bool doMerge = false;
            Expression addedAssert = null;
            if (oldS is VarDeclStmt) {
              var cOld = (VarDeclStmt)oldS;
              if (VarDeclAgree(cOld.Lhss, cNew.Lhss)) {
                var update = cNew.Update as UpdateStmt;
                if (update != null && update.Rhss.TrueForAll(rhs => !rhs.CanAffectPreviouslyKnownExpressions)) {
                  // Note, we allow switching between ghost and non-ghost, since that seems unproblematic.
                  if (cOld.Update == null) {
                    doMerge = true;
                  } else if (cOld.Update is AssignSuchThatStmt) {
                    doMerge = true;
                    addedAssert = refinementCloner.CloneExpr(((AssignSuchThatStmt)cOld.Update).Expr);
                  } else {
                    var updateOld = (UpdateStmt)cOld.Update;  // if cast fails, there are more ConcreteUpdateStatement subclasses than expected
                    doMerge = true;
                    foreach (var rhs in updateOld.Rhss) {
                      if (!(rhs is HavocRhs))
                        doMerge = false;
                    }
                  }
                }
              }
            }
            if (doMerge) {
              // Go ahead with the merge:
              body.Add(cNew);
              i++; j++;
              if (addedAssert != null) {
                body.Add(new AssertStmt(new Translator.ForceCheckToken(addedAssert.tok), addedAssert, null));
              }
            } else {
              MergeAddStatement(cur, body);
              i++;
            }

          } else if (cur is AssignStmt) {
            var cNew = (AssignStmt)cur;
            var cOld = oldS as AssignStmt;
            if (cOld == null && oldS is UpdateStmt) {
              var us = (UpdateStmt)oldS;
              if (us.ResolvedStatements.Count == 1) {
                cOld = us.ResolvedStatements[0] as AssignStmt;
              }
            }
            bool doMerge = false;
            if (cOld != null && cNew.Lhs.Resolved is IdentifierExpr && cOld.Lhs.Resolved is IdentifierExpr) {
              if (((IdentifierExpr)cNew.Lhs.Resolved).Name == ((IdentifierExpr)cOld.Lhs.Resolved).Name) {
                if (!(cNew.Rhs is TypeRhs) && cOld.Rhs is HavocRhs) {
                  doMerge = true;
                }
              }
            }
            if (doMerge) {
              // Go ahead with the merge:
              body.Add(cNew);
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }

          } else if (cur is UpdateStmt) {
            var nw = (UpdateStmt)cur;
            List<Statement> stmtGenerated = new List<Statement>();
            bool doMerge = false;
            if (oldS is UpdateStmt) {
              var s = (UpdateStmt)oldS;
              if (LeftHandSidesAgree(s.Lhss, nw.Lhss)) {
                doMerge = true;
                stmtGenerated.Add(nw);
                foreach (var rhs in s.Rhss) {
                  if (!(rhs is HavocRhs))
                    doMerge = false;
                }
              }
            } else if (oldS is AssignSuchThatStmt) {
              var s = (AssignSuchThatStmt)oldS;
              if (LeftHandSidesAgree(s.Lhss, nw.Lhss)) {
                doMerge = true;
                stmtGenerated.Add(nw);
                var addedAssert = refinementCloner.CloneExpr(s.Expr);
                stmtGenerated.Add(new AssertStmt(new Translator.ForceCheckToken(addedAssert.tok), addedAssert, null));
              }
            }
            if (doMerge) {
              // Go ahead with the merge:
              Contract.Assert(cce.NonNullElements(stmtGenerated));
              body.AddRange(stmtGenerated);
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }
          } else if (cur is IfStmt) {
            var cNew = (IfStmt)cur;
            var cOld = oldS as IfStmt;
            if (cOld != null && cOld.Guard == null) {
              var r = new IfStmt(cNew.Tok, cNew.Guard, MergeBlockStmt(cNew.Thn, cOld.Thn), MergeElse(cNew.Els, cOld.Els));
              body.Add(r);
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }

          } else if (cur is WhileStmt) {
            var cNew = (WhileStmt)cur;
            var cOld = oldS as WhileStmt;
            if (cOld != null && cOld.Guard == null) {
              var r = MergeWhileStmt(cNew, cOld, cNew.Guard);
              body.Add(r);
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }

          } else if (cur is BlockStmt) {
            var cNew = (BlockStmt)cur;
            var cOld = oldS as BlockStmt;
            if (cOld != null) {
              var r = MergeBlockStmt(cNew, cOld);
              body.Add(r);
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }
          } else {
            MergeAddStatement(cur, body);
            i++;
          }
        }
      }
      // implement the implicit "...;" at the end of each block statement skeleton
      for (; j < oldStmt.Body.Count; j++) {
        body.Add(refinementCloner.CloneStmt(oldStmt.Body[j]));
      }
      return new BlockStmt(skeleton.Tok, body);
    }

    private bool LeftHandSidesAgree(List<Expression> old, List<Expression> nw) {
      if (old.Count != nw.Count)
        return false;
      for (int i = 0; i < old.Count; i++) {
        var a = old[i].Resolved as IdentifierExpr;
        var b = nw[i] as IdentifierSequence;
        if (a != null && b != null)
          if (b.Tokens.Count == 1 && b.Arguments == null)
            if (a.Name == b.Tokens[0].val)
              continue;
        return false;
      }
      return true;
    }
    private bool VarDeclAgree(List<VarDecl> old, List<VarDecl> nw) {
      if (old.Count != nw.Count)
        return false;
      for (int i = 0; i < old.Count; i++) {
        if (old[i].Name != nw[i].Name)
          return false;
      }
      return true;
    }

    bool PotentialMatch(Statement nxt, Statement other) {
      Contract.Requires(nxt != null);
      Contract.Requires(!(nxt is SkeletonStatement) || ((SkeletonStatement)nxt).S != null);  // nxt is not "...;"
      Contract.Requires(other != null);

      if (nxt.Labels != null) {
        for (var olbl = other.Labels; olbl != null; olbl = olbl.Next) {
          var odata = olbl.Data;
          for (var l = nxt.Labels; l != null; l = l.Next) {
            if (odata.Name == l.Data.Name) {
              return true;
            }
          }
        }
        return false;  // labels of 'nxt' don't match any label of 'other'
      } else  if (nxt is SkeletonStatement) {
        var S = ((SkeletonStatement)nxt).S;
        if (S is AssertStmt) {
          return other is PredicateStmt;
        } else if (S is AssumeStmt) {
          return other is AssumeStmt;
        } else if (S is IfStmt) {
          return other is IfStmt;
        } else if (S is WhileStmt) {
          return other is WhileStmt;
        } else {
          Contract.Assume(false);  // unexpected skeleton
        }

      } else if (nxt is IfStmt) {
        var oth = other as IfStmt;
        return oth != null && oth.Guard == null;
      } else if (nxt is WhileStmt) {
        var oth = other as WhileStmt;
        return oth != null && oth.Guard == null;
      } else if (nxt is VarDeclStmt) {
        var oth = other as VarDeclStmt;
        return oth != null && VarDeclAgree(((VarDeclStmt)nxt).Lhss, oth.Lhss);
      } else if (nxt is BlockStmt) {
        var b = (BlockStmt)nxt;
        if (b.Labels != null) {
          var oth = other as BlockStmt;
          if (oth != null && oth.Labels != null) {
            return b.Labels.Data.Name == oth.Labels.Data.Name; // both have the same label
          }
        } else if (other is BlockStmt && ((BlockStmt)other).Labels == null) {
          return true; // both are unlabeled
        }
      } else if (nxt is UpdateStmt) {
        var up = (UpdateStmt)nxt;
        if (other is AssignSuchThatStmt) {
          var oth = other as AssignSuchThatStmt;
          return oth != null && LeftHandSidesAgree(oth.Lhss, up.Lhss);
        }
      }

      // not a potential match
      return false;
    }

    WhileStmt MergeWhileStmt(WhileStmt cNew, WhileStmt cOld, Expression guard) {
      Contract.Requires(cNew != null);
      Contract.Requires(cOld != null);

      // Note, the parser produces errors if there are any decreases or modifies clauses (and it creates
      // the Specification structures with a null list).
      Contract.Assume(cNew.Mod.Expressions == null);

      // If the previous loop was not specified with "decreases *", then the new loop is not allowed to provide any "decreases" clause.
      // Any "decreases *" clause is not inherited, so if the previous loop was specified with "decreases *", then the new loop needs
      // to either redeclare "decreases *", provided a termination-checking "decreases" clause, or give no "decreases" clause and thus
      // get a default "decreases" loop.
      Specification<Expression> decr;
      if (Contract.Exists(cOld.Decreases.Expressions, e => e is WildcardExpr)) {
        decr = cNew.Decreases;  // take the new decreases clauses, whatever they may be (including nothing at all)
      } else {
        if (cNew.Decreases.Expressions.Count != 0) {
          reporter.Error(cNew.Decreases.Expressions[0].tok, "a refining loop can provide a decreases clause only if the loop being refined was declared with 'decreases *'");
        }
        decr = refinementCloner.CloneSpecExpr(cOld.Decreases);
      }

      var invs = cOld.Invariants.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
      invs.AddRange(cNew.Invariants);
      var r = new RefinedWhileStmt(cNew.Tok, guard, invs, decr, refinementCloner.CloneSpecFrameExpr(cOld.Mod), MergeBlockStmt(cNew.Body, cOld.Body));
      return r;
    }

    Statement MergeElse(Statement skeleton, Statement oldStmt) {
      Contract.Requires(skeleton == null || skeleton is BlockStmt || skeleton is IfStmt || skeleton is SkeletonStatement);
      Contract.Requires(oldStmt == null || oldStmt is BlockStmt || oldStmt is IfStmt || oldStmt is SkeletonStatement);

      if (skeleton == null) {
        return refinementCloner.CloneStmt(oldStmt);
      } else if (skeleton is IfStmt || skeleton is SkeletonStatement) {
        // wrap a block statement around the if statement
        skeleton = new BlockStmt(skeleton.Tok, new List<Statement>() { skeleton });
      }

      if (oldStmt == null) {
        // make it into an empty block statement
        oldStmt = new BlockStmt(skeleton.Tok, new List<Statement>());
      } else if (oldStmt is IfStmt || oldStmt is SkeletonStatement) {
        // wrap a block statement around the if statement
        oldStmt = new BlockStmt(oldStmt.Tok, new List<Statement>() { oldStmt });
      }

      Contract.Assert(skeleton is BlockStmt && oldStmt is BlockStmt);
      return MergeBlockStmt((BlockStmt)skeleton, (BlockStmt)oldStmt);
    }

    /// <summary>
    /// Add "s" to "stmtList", but complain if "s" contains further occurrences of "...", if "s" assigns to a
    /// variable that was not declared in the refining module, or if "s" has some control flow that jumps to a
    /// place outside "s".
    /// </summary>
    void MergeAddStatement(Statement s, List<Statement> stmtList) {
      Contract.Requires(s != null);
      Contract.Requires(stmtList != null);
      var prevErrorCount = reporter.ErrorCount;
      CheckIsOkayNewStatement(s, new Stack<string>(), 0);
      if (reporter.ErrorCount == prevErrorCount) {
        stmtList.Add(s);
      }
    }

    /// <summary>
    /// See comment on MergeAddStatement.
    /// </summary>
    void CheckIsOkayNewStatement(Statement s, Stack<string> labels, int loopLevels) {
      Contract.Requires(s != null);
      Contract.Requires(labels != null);
      Contract.Requires(0 <= loopLevels);

      for (LList<Label> n = s.Labels; n != null; n = n.Next) {
        labels.Push(n.Data.Name);
      }
      if (s is SkeletonStatement) {
        reporter.Error(s, "skeleton statement may not be used here; it does not have a matching statement in what is being replaced");
      } else if (s is ReturnStmt) {
        // allow return statements, but make note of that this requires verifying the postcondition
        ((ReturnStmt)s).ReverifyPost = true;
      } else if (s is YieldStmt) {
        reporter.Error(s, "yield statements are not allowed in skeletons");
      } else if (s is BreakStmt) {
        var b = (BreakStmt)s;
        if (b.TargetLabel != null ? !labels.Contains(b.TargetLabel) : loopLevels < b.BreakCount) {
          reporter.Error(s, "break statement in skeleton is not allowed to break outside the skeleton fragment");
        }
      } else if (s is AssignStmt) {
        // TODO: To be a refinement automatically (that is, without any further verification), only variables and fields defined
        // in this module are allowed.  This needs to be checked.  If the LHS refers to an l-value that was not declared within
        // this module, then either an error should be reported or the Translator needs to know to translate new proof obligations.
        var a = (AssignStmt)s;
        reporter.Error(a.Tok, "cannot have assignment statement");
      } else if (s is ConcreteUpdateStatement) {
        postTasks.Enqueue(() =>
        {
          CheckIsOkayUpdateStmt((ConcreteUpdateStatement)s, moduleUnderConstruction, reporter);
        });
      } else if (s is CallStmt) {
        reporter.Error(s.Tok, "cannot have call statement");
      } else if (s is ForallStmt) {
        if (((ForallStmt)s).Kind == ForallStmt.ParBodyKind.Assign) // allow Proof and Call (as neither touch any existing state)
          reporter.Error(s.Tok, "cannot have forall statement");
      } else {
        if (s is WhileStmt || s is AlternativeLoopStmt) {
          loopLevels++;
        }
        foreach (var ss in s.SubStatements) {
          CheckIsOkayNewStatement(ss, labels, loopLevels);
        }
      }

      for (LList<Label> n = s.Labels; n != null; n = n.Next) {
        labels.Pop();
      }
    }

    // Checks that statement stmt, defined in the constructed module m, is a refinement of skip in the parent module
    private bool CheckIsOkayUpdateStmt(ConcreteUpdateStatement stmt, ModuleDefinition m, ResolutionErrorReporter reporter) {
      foreach (var lhs in stmt.Lhss) {
        var l = lhs.Resolved;
        if (l is IdentifierExpr) {
          var ident = (IdentifierExpr)l;
          Contract.Assert(ident.Var is VarDecl || ident.Var is Formal); // LHS identifier expressions must be locals or out parameters (ie. formals)
          if ((ident.Var is VarDecl && RefinementToken.IsInherited(((VarDecl)ident.Var).Tok, m)) || ident.Var is Formal) {
            // for some reason, formals are not considered to be inherited.
            reporter.Error(l.tok, "cannot assign to variable defined previously");
            return false;
          }
        } else if (l is FieldSelectExpr) {
          if (RefinementToken.IsInherited(((FieldSelectExpr)l).Field.tok, m)) {
            return false;
          }
        } else {
          return false;
        }
      }
      if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var rhs in s.Rhss) {
          if (s.Rhss[0].CanAffectPreviouslyKnownExpressions) {
            return false;
          }
        }
      }
      return true;
    }
    // ---------------------- additional methods -----------------------------------------------------------------------------

    public static bool ContainsChange(Expression expr, ModuleDefinition m) {
      Contract.Requires(expr != null);
      Contract.Requires(m != null);

      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function.EnclosingClass.Module == m) {
          var p = e.Function as Predicate;
          if (p != null && p.BodyOrigin == Predicate.BodyOriginKind.Extension) {
            return true;
          }
        }
      }

      foreach (var ee in expr.SubExpressions) {
        if (ContainsChange(ee, m)) {
          return true;
        }
      }
      return false;
    }
  }

  class RefinementCloner : Cloner {
    ModuleDefinition moduleUnderConstruction;
    public RefinementCloner(ModuleDefinition m) {
      moduleUnderConstruction = m;
    }
    public override IToken Tok(IToken tok) {
      return new RefinementToken(tok, moduleUnderConstruction);
    }
    public virtual Attributes MergeAttributes(Attributes prevAttrs, Attributes moreAttrs) {
      if (moreAttrs == null) {
        return CloneAttributes(prevAttrs);
      } else {
        return new Attributes(moreAttrs.Name, moreAttrs.Args.ConvertAll(CloneAttrArg), MergeAttributes(prevAttrs, moreAttrs.Prev));
      }
    }
  }
  class SubstitutionCloner : Cloner {
    public Dictionary<string, Expression> Exprs;
    public SortedSet<string> SubstitutionsMade;
    Cloner c;
    public SubstitutionCloner(Dictionary<string, Expression> subs, Cloner c) {
      Exprs = subs;
      SubstitutionsMade = new SortedSet<string>();
      this.c = c;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is NamedExpr) {
        NamedExpr n = (NamedExpr)expr;
        Expression E;
        if (Exprs.TryGetValue(n.Name, out E)) {
          SubstitutionsMade.Add(n.Name);
          return new NamedExpr(n.tok, n.Name, E, c.CloneExpr(n.Body), E.tok);
        }
      } 
      return base.CloneExpr(expr); // in all other cases, just do what the base class would.
                                   // note that when we get a named expression that is not in
                                   // our substitution list, then we call the base class, which
                                   // recurses on the body of the named expression.
    }
  }
}