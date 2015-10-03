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
    Cloner rawCloner; // This cloner just gives exactly the same thing back.
    RefinementCloner refinementCloner; // This cloner wraps things in a RefinementTransformer
    
    Program program;

    public RefinementTransformer(ErrorReporter reporter)
      : base(reporter) {
      rawCloner = new Cloner();
    }

    public RefinementTransformer(Program p)
      : this(p.reporter) {
      Contract.Requires(p != null);
      program = p;
    }

    private ModuleDefinition moduleUnderConstruction;  // non-null for the duration of Construct calls
    private Queue<Action> postTasks = new Queue<Action>();  // empty whenever moduleUnderConstruction==null, these tasks are for the post-resolve phase of module moduleUnderConstruction
    public Queue<Tuple<Method, Method>> translationMethodChecks = new Queue<Tuple<Method, Method>>();  // contains all the methods that need to be checked for structural refinement.
    private Method currentMethod;
    public ModuleSignature RefinedSig;  // the intention is to use this field only after a successful PreResolve

    internal override void PreResolve(ModuleDefinition m) {
      if (m.RefinementBaseRoot != null) {
        if (Resolver.ResolvePath(m.RefinementBaseRoot, m.RefinementBaseName, out RefinedSig, reporter)) {
          if (RefinedSig.ModuleDef != null) {
            m.RefinementBase = RefinedSig.ModuleDef;
            if (m.IsExclusiveRefinement) {
              if (null == m.RefinementBase.ExclusiveRefinement) {
                m.RefinementBase.ExclusiveRefinement = m;
              } else {
                reporter.Error(MessageSource.RefinementTransformer,
                    m.tok,
                    "no more than one exclusive refinement may exist for a given module.");
              }
            }
            PreResolveWorker(m);
          } else {
            reporter.Error(MessageSource.RefinementTransformer, m.RefinementBaseName[0], "module ({0}) named as refinement base is not a literal module or simple reference to a literal module", Util.Comma(".", m.RefinementBaseName, x => x.val));
          }
        } else {
          reporter.Error(MessageSource.RefinementTransformer, m.RefinementBaseName[0], "module ({0}) named as refinement base does not exist", Util.Comma(".", m.RefinementBaseName, x => x.val));
        }
      }
    }
    
    void PreResolveWorker(ModuleDefinition m) {
      Contract.Requires(m != null);

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
              reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
            } else if (!(d is ModuleFacadeDecl)) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) can only refine a module facade", nw.Name);
            } else {
              ModuleSignature original = ((ModuleFacadeDecl)d).OriginalSignature;
              ModuleSignature derived = null;
              if (nw is AliasModuleDecl) {
                derived = ((AliasModuleDecl)nw).Signature;
              } else if (nw is ModuleFacadeDecl) {
                derived = ((ModuleFacadeDecl)nw).Signature;
              } else {
                reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) can only be refined by an alias module or a module facade", d.Name);
              }
              if (derived != null) {
                // check that the new module refines the previous declaration
                if (!CheckIsRefinement(derived, original))
                  reporter.Error(MessageSource.RefinementTransformer, nw.tok, "a module ({0}) can only be replaced by a refinement of the original module", d.Name);
              }
            }
          } else if (d is OpaqueTypeDecl) {
            if (nw is ModuleDecl) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              bool dDemandsEqualitySupport = ((OpaqueTypeDecl)d).MustSupportEquality;
              if (nw is OpaqueTypeDecl) {
                if (dDemandsEqualitySupport != ((OpaqueTypeDecl)nw).MustSupportEquality) {
                  reporter.Error(MessageSource.RefinementTransformer, nw, "type declaration '{0}' is not allowed to change the requirement of supporting equality", nw.Name);
                }
                if (nw.TypeArgs.Count != d.TypeArgs.Count) {
                  reporter.Error(MessageSource.RefinementTransformer, nw, "type '{0}' is not allowed to change its number of type parameters (got {1}, expected {2})", nw.Name, nw.TypeArgs.Count, d.TypeArgs.Count);
                }
              } else if (dDemandsEqualitySupport) {
                if (nw is ClassDecl) {
                  // fine, as long as "nw" takes the right number of type parameters
                  if (nw.TypeArgs.Count != d.TypeArgs.Count) {
                    reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}' is not allowed to be replaced by a class that takes a different number of type parameters (got {1}, expected {2})", nw.Name, nw.TypeArgs.Count, d.TypeArgs.Count);
                  }
                } else if (nw is NewtypeDecl) {
                  // fine, as long as "nw" does not take any type parameters
                  if (nw.TypeArgs.Count != 0) {
                    reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}', which has {1} type argument{2}, is not allowed to be replaced by a newtype, which takes none", nw.Name, d.TypeArgs.Count, d.TypeArgs.Count == 1 ? "" : "s");
                  }
                } else if (nw is CoDatatypeDecl) {
                  reporter.Error(MessageSource.RefinementTransformer, nw, "a type declaration that requires equality support cannot be replaced by a codatatype");
                } else {
                  Contract.Assert(nw is IndDatatypeDecl || nw is TypeSynonymDecl);
                  if (nw.TypeArgs.Count != d.TypeArgs.Count) {
                    reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}' is not allowed to be replaced by a type that takes a different number of type parameters (got {1}, expected {2})", nw.Name, nw.TypeArgs.Count, d.TypeArgs.Count);
                  } else {
                    // Here, we need to figure out if the new type supports equality.  But we won't know about that until resolution has
                    // taken place, so we defer it until the PostResolve phase.
                    var udt = UserDefinedType.FromTopLevelDecl(nw.tok, nw);
                    postTasks.Enqueue(() => {
                      if (!udt.SupportsEquality) {
                        reporter.Error(MessageSource.RefinementTransformer, udt.tok, "type '{0}' is used to refine an opaque type with equality support, but '{0}' does not support equality", udt.Name);
                      }
                    });
                  }
                }
              } else if (d.TypeArgs.Count != nw.TypeArgs.Count) {
                reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}' is not allowed to be replaced by a type that takes a different number of type parameters (got {1}, expected {2})", nw.Name, nw.TypeArgs.Count, d.TypeArgs.Count);
              }
            }
          } else if (nw is OpaqueTypeDecl) {
            reporter.Error(MessageSource.RefinementTransformer, nw, "an opaque type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
          } else if (nw is DatatypeDecl) {
            reporter.Error(MessageSource.RefinementTransformer, nw, "a datatype declaration ({0}) in a refinement module can only replace an opaque type declaration", nw.Name);
          } else if (nw is IteratorDecl) {
            if (d is IteratorDecl) {
              m.TopLevelDecls[index] = MergeIterator((IteratorDecl)nw, (IteratorDecl)d);
            } else {
              reporter.Error(MessageSource.RefinementTransformer, nw, "an iterator declaration ({0}) is a refining module cannot replace a different kind of declaration in the refinement base", nw.Name);
            }
          } else {
            Contract.Assert(nw is ClassDecl);
            if (d is DatatypeDecl) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a class declaration ({0}) in a refining module cannot replace a different kind of declaration in the refinement base", nw.Name);
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

      var errorCount = reporter.Count(ErrorLevel.Error);
      foreach (var kv in original.TopLevels) {
        var d = kv.Value;
        TopLevelDecl nw;
        if (derived.TopLevels.TryGetValue(kv.Key, out nw)) {
          if (d is ModuleDecl) {
            if (!(nw is ModuleDecl)) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              CheckIsRefinement(((ModuleDecl)nw).Signature, ((ModuleDecl)d).Signature);
            }
          } else if (d is OpaqueTypeDecl) {
            if (nw is ModuleDecl) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
            } else {
              bool dDemandsEqualitySupport = ((OpaqueTypeDecl)d).MustSupportEquality;
              if (nw is OpaqueTypeDecl) {
                if (dDemandsEqualitySupport != ((OpaqueTypeDecl)nw).MustSupportEquality) {
                  reporter.Error(MessageSource.RefinementTransformer, nw, "type declaration '{0}' is not allowed to change the requirement of supporting equality", nw.Name);
                }
              } else if (dDemandsEqualitySupport) {
                if (nw is ClassDecl) {
                  // fine, as long as "nw" does not take any type parameters
                  if (nw.TypeArgs.Count != 0) {
                    reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}' is not allowed to be replaced by a class that takes type parameters", nw.Name);
                  }
                } else if (nw is CoDatatypeDecl) {
                  reporter.Error(MessageSource.RefinementTransformer, nw, "a type declaration that requires equality support cannot be replaced by a codatatype");
                } else {
                  Contract.Assert(nw is IndDatatypeDecl);
                  if (nw.TypeArgs.Count != 0) {
                    reporter.Error(MessageSource.RefinementTransformer, nw, "opaque type '{0}' is not allowed to be replaced by a datatype that takes type parameters", nw.Name);
                  } else {
                    var udt = new UserDefinedType(nw.tok, nw.Name, nw, new List<Type>());
                    if (!(udt.SupportsEquality)) {
                      reporter.Error(MessageSource.RefinementTransformer, nw.tok, "datatype '{0}' is used to refine an opaque type with equality support, but '{0}' does not support equality", nw.Name);
                    }
                  }
                }
              }
            }
          } else if (d is DatatypeDecl) {
            if (nw is DatatypeDecl) {
              if (d is IndDatatypeDecl && !(nw is IndDatatypeDecl)) {
                reporter.Error(MessageSource.RefinementTransformer, nw, "a datatype ({0}) must be replaced by a datatype, not a codatatype", d.Name);
              } else if (d is CoDatatypeDecl && !(nw is CoDatatypeDecl)) {
                reporter.Error(MessageSource.RefinementTransformer, nw, "a codatatype ({0}) must be replaced by a codatatype, not a datatype", d.Name);
              }
              // check constructors, formals, etc.
              CheckDatatypesAreRefinements((DatatypeDecl)d, (DatatypeDecl)nw);
            } else {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a {0} ({1}) must be refined by a {0}", d is IndDatatypeDecl ? "datatype" : "codatatype", d.Name);
            }
          } else if (d is ClassDecl) {
            if (!(nw is ClassDecl)) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "a class declaration ({0}) must be refined by another class declaration", nw.Name);
            } else {
              CheckClassesAreRefinements((ClassDecl)nw, (ClassDecl)d);
            }
          } else {
            Contract.Assert(false); throw new cce.UnreachableException(); // unexpected toplevel
          }
        } else {
          reporter.Error(MessageSource.RefinementTransformer, d, "declaration {0} must have a matching declaration in the refining module", d.Name);
        }
      }
      return errorCount == reporter.Count(ErrorLevel.Error);
    }

    private void CheckClassesAreRefinements(ClassDecl nw, ClassDecl d) {
      if (nw.TypeArgs.Count != d.TypeArgs.Count) {
        reporter.Error(MessageSource.RefinementTransformer, nw, "a refining class ({0}) must have the same number of type parameters", nw.Name);
      } else {
        var map = new Dictionary<string, MemberDecl>();
        foreach (var mem in nw.Members) {
          map.Add(mem.Name, mem);
        }
        foreach (var m in d.Members) {
          MemberDecl newMem;
          if (map.TryGetValue(m.Name, out newMem)) {
            if (m.HasStaticKeyword != newMem.HasStaticKeyword) {
              reporter.Error(MessageSource.RefinementTransformer, newMem, "member {0} must {1}", m.Name, m.HasStaticKeyword ? "be static" : "not be static");
            }
            if (m is Field) {
              if (newMem is Field) {
                var newField = (Field)newMem;
                if (!ResolvedTypesAreTheSame(newField.Type, ((Field)m).Type))
                  reporter.Error(MessageSource.RefinementTransformer, newMem, "field must be refined by a field with the same type (got {0}, expected {1})", newField.Type, ((Field)m).Type);
                if (m.IsGhost || !newField.IsGhost)
                  reporter.Error(MessageSource.RefinementTransformer, newField, "a field re-declaration ({0}) must be to ghostify the field", newField.Name, nw.Name);
              } else {
                reporter.Error(MessageSource.RefinementTransformer, newMem, "a field declaration ({1}) must be replaced by a field in the refinement base (not {0})", newMem.Name, nw.Name);
              }
            } else if (m is Method) {
              if (newMem is Method) {
                CheckMethodsAreRefinements((Method)newMem, (Method)m);
              } else {
                reporter.Error(MessageSource.RefinementTransformer, newMem, "method must be refined by a method");
              }
            } else if (m is Function) {
              if (newMem is Function) {
                CheckFunctionsAreRefinements((Function)newMem, (Function)m);
              } else {
                reporter.Error(MessageSource.RefinementTransformer, newMem, "{0} must be refined by a {0}", m.WhatKind);
              }
            }
          } else {
            reporter.Error(MessageSource.RefinementTransformer, nw is DefaultClassDecl ? nw.Module.tok : nw.tok, "refining {0} must have member {1}", nw is DefaultClassDecl ? "module" : "class", m.Name);
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
        reporter.Error(MessageSource.RefinementTransformer, tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (!o.IsGhost && n.IsGhost) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!ResolvedTypesAreTheSame(o.Type, n.Type)) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
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
          reporter.Error(MessageSource.RefinementTransformer, nw, "a predicate declaration ({0}) can only be refined by a predicate", nw.Name);
        } else {
          CheckAgreement_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "predicate", false);
          CheckAgreementResolvedParameters(nw.tok, f.Formals, nw.Formals, nw.Name, "predicate", "parameter");
        }
      } else if (f is FixpointPredicate) {
        reporter.Error(MessageSource.RefinementTransformer, nw, "refinement of {0}s is not supported", f.WhatKind);
      } else {
        // f is a plain Function
        if (nw is Predicate || nw is FixpointPredicate) {
          reporter.Error(MessageSource.RefinementTransformer, nw, "a {0} declaration ({1}) can only be refined by a function or function method", nw.IsGhost ? "function" : "function method", nw.Name);
        } else {
          CheckAgreement_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "function", false);
          CheckAgreementResolvedParameters(nw.tok, f.Formals, nw.Formals, nw.Name, "function", "parameter");
          if (!ResolvedTypesAreTheSame(nw.ResultType, f.ResultType)) {
            reporter.Error(MessageSource.RefinementTransformer, nw, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", nw.Name, nw.ResultType, f.ResultType);
          }
        }
      }
      program.TranslationTasks.Add(new FunctionCheck(nw, f));
    }


    private void CheckDatatypesAreRefinements(DatatypeDecl dd, DatatypeDecl nn) {
      CheckAgreement_TypeParameters(nn.tok, dd.TypeArgs, nn.TypeArgs, dd.Name, "datatype", false);
      if (dd.Ctors.Count != nn.Ctors.Count) {
        reporter.Error(MessageSource.RefinementTransformer, nn.tok, "a refining datatype must have the same number of constructors");
      } else {
        var map = new Dictionary<string, DatatypeCtor>();
        foreach (var ctor in nn.Ctors) {
          map.Add(ctor.Name, ctor);
        }
        foreach (var ctor in dd.Ctors) {
          DatatypeCtor newCtor;
          if (map.TryGetValue(ctor.Name, out newCtor)) {
            if (newCtor.Formals.Count != ctor.Formals.Count) {
              reporter.Error(MessageSource.RefinementTransformer, newCtor, "the constructor ({0}) must have the same number of formals as in the refined module", newCtor.Name);
            } else {
              for (int i = 0; i < newCtor.Formals.Count; i++) {
                var a = ctor.Formals[i]; var b = newCtor.Formals[i];
                if (a.HasName) {
                  if (!b.HasName || a.Name != b.Name)
                    reporter.Error(MessageSource.RefinementTransformer, b, "formal argument {0} in constructor {1} does not have the same name as in the refined module (should be {2})", i, ctor.Name, a.Name);
                }
                if (!ResolvedTypesAreTheSame(a.Type, b.Type)) {
                  reporter.Error(MessageSource.RefinementTransformer, b, "formal argument {0} in constructor {1} does not have the same type as in the refined module (should be {2}, not {3})", i, ctor.Name, a.Type.ToString(), b.Type.ToString());
                }
              }
            }
          } else {
            reporter.Error(MessageSource.RefinementTransformer, nn, "the constructor {0} must be present in the refining datatype", ctor.Name);
          }
        }
      }
      
    }
    // Check that two resolved types are the same in a similar context (the same type parameters, method, class, etc.)
    // Assumes that prev is in a previous refinement, and next is in some refinement. Note this is not communative.
    public static bool ResolvedTypesAreTheSame(Type prev, Type next) {
      Contract.Requires(prev != null);
      Contract.Requires(next != null);
      prev = prev.NormalizeExpand();
      next = next.NormalizeExpand();
      if (prev is TypeProxy || next is TypeProxy)
        return false;

      if (prev is BoolType) {
        return next is BoolType;
      } else if (prev is CharType) {
        return next is CharType;
      } else if (prev is IntType) {
        if (next is IntType) {
          return (prev is NatType) == (next is NatType);
        } else return false;
      } else if (prev is RealType) {
        return next is RealType;
      } else if (prev is ObjectType) {
        return next is ObjectType;
      } else if (prev is SetType) {
        return next is SetType && ((SetType)prev).Finite == ((SetType)next).Finite &&
          ResolvedTypesAreTheSame(((SetType)prev).Arg, ((SetType)next).Arg);
      } else if (prev is MultiSetType) {
        return next is MultiSetType && ResolvedTypesAreTheSame(((MultiSetType)prev).Arg, ((MultiSetType)next).Arg);
      } else if (prev is MapType) {
        return next is MapType && ((MapType)prev).Finite == ((MapType)next).Finite &&
               ResolvedTypesAreTheSame(((MapType)prev).Domain, ((MapType)next).Domain) && ResolvedTypesAreTheSame(((MapType)prev).Range, ((MapType)next).Range);
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

    internal override void PostResolve(ModuleDefinition m) {
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
        return new Predicate(tok, f.Name, f.HasStaticKeyword, f.IsProtected, isGhost, tps, formals,
          req, reads, ens, decreases, body, bodyOrigin, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null, f);
      } else if (f is InductivePredicate) {
        return new InductivePredicate(tok, f.Name, f.HasStaticKeyword, f.IsProtected, tps, formals,
          req, reads, ens, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null, f);
      } else if (f is CoPredicate) {
        return new CoPredicate(tok, f.Name, f.HasStaticKeyword, f.IsProtected, tps, formals,
          req, reads, ens, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null, f);
      } else {
        return new Function(tok, f.Name, f.HasStaticKeyword, f.IsProtected, isGhost, tps, formals, refinementCloner.CloneType(f.ResultType),
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null, f);
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
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null, m);
      } else if (m is InductiveLemma) {
        return new InductiveLemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null, m);
      } else if (m is CoLemma) {
        return new CoLemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null, m);
      } else if (m is Lemma) {
        return new Lemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null, m);
      } else {
        return new Method(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, m.IsGhost, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null, m);
      }
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    IteratorDecl MergeIterator(IteratorDecl nw, IteratorDecl prev) {
      Contract.Requires(nw != null);
      Contract.Requires(prev != null);

      if (nw.Requires.Count != 0) {
        reporter.Error(MessageSource.RefinementTransformer, nw.Requires[0].E.tok, "a refining iterator is not allowed to add preconditions");
      }
      if (nw.YieldRequires.Count != 0) {
        reporter.Error(MessageSource.RefinementTransformer, nw.YieldRequires[0].E.tok, "a refining iterator is not allowed to add yield preconditions");
      }
      if (nw.Reads.Expressions.Count != 0) {
        reporter.Error(MessageSource.RefinementTransformer, nw.Reads.Expressions[0].E.tok, "a refining iterator is not allowed to extend the reads clause");
      }
      if (nw.Modifies.Expressions.Count != 0) {
        reporter.Error(MessageSource.RefinementTransformer, nw.Modifies.Expressions[0].E.tok, "a refining iterator is not allowed to extend the modifies clause");
      }
      if (nw.Decreases.Expressions.Count != 0) {
        reporter.Error(MessageSource.RefinementTransformer, nw.Decreases.Expressions[0].tok, "a refining iterator is not allowed to extend the decreases clause");
      }

      if (nw.SignatureIsOmitted) {
        Contract.Assert(nw.TypeArgs.Count == 0);
        Contract.Assert(nw.Ins.Count == 0);
        Contract.Assert(nw.Outs.Count == 0);
        reporter.Info(MessageSource.RefinementTransformer, nw.SignatureEllipsis, Printer.IteratorSignatureToString(prev));
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

      return new IteratorDecl(new RefinementToken(nw.tok, moduleUnderConstruction),
        nw.Name, moduleUnderConstruction,
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
        null);
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
                reporter.Error(MessageSource.RefinementTransformer, nwMember, "a field re-declaration ({0}) must be to ghostify the field", nwMember.Name, nw.Name);
            } else {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a field declaration ({0}) in a refining class ({1}) must replace a field in the refinement base", nwMember.Name, nw.Name);
            }
            nwMember.RefinementBase = member;

          } else if (nwMember is Function) {
            var f = (Function)nwMember;
            bool isPredicate = f is Predicate;
            bool isIndPredicate = f is InductivePredicate;
            bool isCoPredicate = f is CoPredicate;
            if (!(member is Function) ||
              (isPredicate && !(member is Predicate)) ||
              (isIndPredicate && !(member is InductivePredicate)) ||
              (isCoPredicate && !(member is CoPredicate))) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a {0} declaration ({1}) can only refine a {0}", f.WhatKind, nwMember.Name);
            } else if (f.IsProtected != ((Function)member).IsProtected) {
              reporter.Error(MessageSource.RefinementTransformer, f, "a {0} in a refinement module must be declared 'protected' if and only if the refined {0} is", f.WhatKind);
            } else {
              var prevFunction = (Function)member;
              if (f.Req.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, f.Req[0].tok, "a refining {0} is not allowed to add preconditions", f.WhatKind);
              }
              if (f.Reads.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, f.Reads[0].E.tok, "a refining {0} is not allowed to extend the reads clause", f.WhatKind);
              }
              if (f.Decreases.Expressions.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, f.Decreases.Expressions[0].tok, "decreases clause on refining {0} not supported", f.WhatKind);
              }

              if (prevFunction.HasStaticKeyword != f.HasStaticKeyword) {
                reporter.Error(MessageSource.RefinementTransformer, f, "a function in a refining module cannot be changed from static to non-static or vice versa: {0}", f.Name);
              }
              if (!prevFunction.IsGhost && f.IsGhost) {
                reporter.Error(MessageSource.RefinementTransformer, f, "a function method cannot be changed into a (ghost) function in a refining module: {0}", f.Name);
              } else if (prevFunction.IsGhost && !f.IsGhost && prevFunction.Body != null) {
                reporter.Error(MessageSource.RefinementTransformer, f, "a function can be changed into a function method in a refining module only if the function has not yet been given a body: {0}", f.Name);
              }
              if (f.SignatureIsOmitted) {
                Contract.Assert(f.TypeArgs.Count == 0);
                Contract.Assert(f.Formals.Count == 0);
                reporter.Info(MessageSource.RefinementTransformer, f.SignatureEllipsis, Printer.FunctionSignatureToString(prevFunction));
              } else {
                CheckAgreement_TypeParameters(f.tok, prevFunction.TypeArgs, f.TypeArgs, f.Name, "function");
                CheckAgreement_Parameters(f.tok, prevFunction.Formals, f.Formals, f.Name, "function", "parameter");
                if (!TypesAreSyntacticallyEqual(prevFunction.ResultType, f.ResultType)) {
                  reporter.Error(MessageSource.RefinementTransformer, f, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", f.Name, f.ResultType, prevFunction.ResultType);
                }
              }

              Expression moreBody = null;
              Expression replacementBody = null;
              if (prevFunction.Body == null) {
                replacementBody = f.Body;
              } else if (f.Body != null) {
                if (isPredicate && f.IsProtected) {
                  moreBody = f.Body;
                } else if (isPredicate) {
                  reporter.Error(MessageSource.RefinementTransformer, nwMember, "a refining predicate is not allowed to extend/change the body unless it is declared 'protected'");
                } else {
                  reporter.Error(MessageSource.RefinementTransformer, nwMember, "a refining function is not allowed to extend/change the body");
                }
              }
              var newF = CloneFunction(f.tok, prevFunction, f.IsGhost, f.Ens, moreBody, replacementBody, prevFunction.Body == null, f.Attributes);
              newF.RefinementBase = member;
              nw.Members[index] = newF;
            }

          } else {
            var m = (Method)nwMember;
            if (!(member is Method)) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a method declaration ({0}) can only refine a method", nwMember.Name);
            } else {
              var prevMethod = (Method)member;
              if (m.Req.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, m.Req[0].E.tok, "a refining method is not allowed to add preconditions");
              }
              if (m.Mod.Expressions.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, m.Mod.Expressions[0].E.tok, "a refining method is not allowed to extend the modifies clause");
              }
              // If the previous method was not specified with "decreases *", then the new method is not allowed to provide any "decreases" clause.
              // Any "decreases *" clause is not inherited, so if the previous method was specified with "decreases *", then the new method needs
              // to either redeclare "decreases *", provided a termination-checking "decreases" clause, or give no "decreases" clause and thus
              // get a default "decreases" loop.
              Specification<Expression> decreases;
              if (m.Decreases.Expressions.Count == 0) {
                // inherited whatever the previous loop used
                decreases = refinementCloner.CloneSpecExpr(prevMethod.Decreases);
              } else {
                if (!Contract.Exists(prevMethod.Decreases.Expressions, e => e is WildcardExpr)) {
                  // If the previous loop was not specified with "decreases *", then the new loop is not allowed to provide any "decreases" clause.
                  reporter.Error(MessageSource.RefinementTransformer, m.Decreases.Expressions[0].tok, "decreases clause on refining method not supported, unless the refined method was specified with 'decreases *'");
                }
                decreases = m.Decreases;
              }
              if (prevMethod.HasStaticKeyword != m.HasStaticKeyword) {
                reporter.Error(MessageSource.RefinementTransformer, m, "a method in a refining module cannot be changed from static to non-static or vice versa: {0}", m.Name);
              }
              if (prevMethod.IsGhost && !m.IsGhost) {
                reporter.Error(MessageSource.RefinementTransformer, m, "a method cannot be changed into a ghost method in a refining module: {0}", m.Name);
              } else if (!prevMethod.IsGhost && m.IsGhost) {
                reporter.Error(MessageSource.RefinementTransformer, m, "a ghost method cannot be changed into a non-ghost method in a refining module: {0}", m.Name);
              }
              if (m.SignatureIsOmitted) {
                Contract.Assert(m.TypeArgs.Count == 0);
                Contract.Assert(m.Ins.Count == 0);
                Contract.Assert(m.Outs.Count == 0);
                reporter.Info(MessageSource.RefinementTransformer, m.SignatureEllipsis, Printer.MethodSignatureToString(prevMethod));
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
        reporter.Error(MessageSource.RefinementTransformer, tok, "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than the corresponding {0} in the module it refines", thing, name, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name && checkNames) { // if checkNames is false, then just treat the parameters positionally.
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameters are not allowed to be renamed from the names given in the {0} in the module being refined (expected '{1}', found '{2}')", thing, o.Name, n.Name);
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
              reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
            }
          }
        }
      }
    }

    public void CheckOverride_FunctionParameters(Function nw, Function f)
    {
        CheckOverride_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "function", false);
        CheckOverrideResolvedParameters(nw.tok, f.Formals, nw.Formals, nw.Name, "function", "parameter");
        if (!ResolvedTypesAreTheSame(nw.ResultType, f.ResultType))
        {
            reporter.Error(MessageSource.RefinementTransformer, nw, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it overrides ({2})", nw.Name, nw.ResultType, f.ResultType);
        }
    }

    public void CheckOverride_MethodParameters(Method nw, Method f)
    {
        CheckOverride_TypeParameters(nw.tok, f.TypeArgs, nw.TypeArgs, nw.Name, "method", false);
        CheckOverrideResolvedParameters(nw.tok, f.Ins, nw.Ins, nw.Name, "method", "in-parameter");
        CheckOverrideResolvedParameters(nw.tok, f.Outs, nw.Outs, nw.Name, "method", "out-parameter");
    }

    public void CheckOverride_TypeParameters(IToken tok, List<TypeParameter> old, List<TypeParameter> nw, string name, string thing, bool checkNames = true)
    {
        Contract.Requires(tok != null);
        Contract.Requires(old != null);
        Contract.Requires(nw != null);
        Contract.Requires(name != null);
        Contract.Requires(thing != null);
        if (old.Count != nw.Count)
        {
            reporter.Error(MessageSource.RefinementTransformer, tok, "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than the corresponding {0} in the module it overrides", thing, name, nw.Count, old.Count);
        }
        else
        {
            for (int i = 0; i < old.Count; i++)
            {
                var o = old[i];
                var n = nw[i];
                if (o.Name != n.Name && checkNames)
                { // if checkNames is false, then just treat the parameters positionally.
                    reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameters are not allowed to be renamed from the names given in the {0} in the module being overriden (expected '{1}', found '{2}')", thing, o.Name, n.Name);
                }
                else
                {
                    // Here's how we actually compute it:
                    if (o.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired && o.EqualitySupport != n.EqualitySupport)
                    {
                        reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
                    }
                }
            }
        }
    }

    public void CheckOverrideResolvedParameters(IToken tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind)
    {
        Contract.Requires(tok != null);
        Contract.Requires(old != null);
        Contract.Requires(nw != null);
        Contract.Requires(name != null);
        Contract.Requires(thing != null);
        Contract.Requires(parameterKind != null);
        if (old.Count != nw.Count)
        {
            reporter.Error(MessageSource.RefinementTransformer, tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it overrides", thing, name, parameterKind, nw.Count, old.Count);
        }
        else
        {
            for (int i = 0; i < old.Count; i++)
            {
                var o = old[i];
                var n = nw[i];
                if (!o.IsGhost && n.IsGhost)
                {
                    reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from non-ghost to ghost", parameterKind, n.Name, thing, name);
                }
                else if (o.IsGhost && !n.IsGhost)
                {
                    reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from ghost to non-ghost", parameterKind, n.Name, thing, name);
                }
                else if (!ResolvedTypesAreTheSame(o.Type, n.Type))
                {
                    reporter.Error(MessageSource.RefinementTransformer, n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it overrides ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
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
        reporter.Error(MessageSource.RefinementTransformer, tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "there is a difference in name of {0} {1} ('{2}' versus '{3}') of {4} {5} compared to corresponding {4} in the module it refines", parameterKind, i, n.Name, o.Name, thing, name);
          } else if (!o.IsGhost && n.IsGhost) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!TypesAreSyntacticallyEqual(o.Type, n.Type)) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
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
            reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "skeleton statement does not match old statement");
          }
          i++;
        } else {
          var oldS = oldStmt.Body[j];
          /* See how the two statements match up.
           *   oldS                         cur                         result
           *   ------                      ------                       ------
           *   assume E;                    assert ...;                 assert E;
           *   assert E;                    assert ...;                 assert E;
           *   assert E;                                                assert E;
           *   
           *   assume E;                    assume ...;                 assume E;
           *   
           *   var x;                       var x := E;                 var x := E;
           *   var x := *;                  var x := E;                 var x := E;
           *   var x :| P;                  var x := E1;                var x := E1; assert P;
           *   var VarProduction;                                       var VarProduction;
           *   
           *   x := *;                      x := E;                     x := E;
           *   x :| P;                      x := E;                     x := E; assert P;
           *   
           *   modify E;                    modify ...;                 modify E;
           *   modify E;                    modify ... { S }            modify E { S }
           *   modify E { S }               modify ... { S' }           modify E { Merge(S, S') }
           *
           *   if (G) Then' else Else'      if ... Then else Else       if (G) Merge(Then,Then') else Merge(Else,Else')
           *   if (*) Then' else Else'      if (G) Then else Else       if (G) Merge(Then,Then') else Merge(Else,Else')
           *   
           *   while (G) LoopSpec' Body     while ... LoopSpec ...      while (G) Merge(LoopSpec,LoopSpec') Body
           *   while (G) LoopSpec' Body'    while ... LoopSpec Body     while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   while (*) LoopSpec' Body     while (G) LoopSpec ...      while (G) Merge(LoopSpec,LoopSpec') Body
           *   while (*) LoopSpec' Body'    while (G) LoopSpec Body     while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   
           *   StmtThatDoesNotMatchS; S'    ... where x = e; S          StatementThatDoesNotMatchS[e/x]; Merge( ... where x = e; S , S')
           *   StmtThatMatchesS; S'         ... where x = e; S          StmtThatMatchesS; S'
           * 
           * Note, LoopSpec must contain only invariant declarations (as the parser ensures for the first three cases).
           * Note, there is an implicit "...;" at the end of every block in a skeleton.
           */
          if (cur is SkeletonStatement) {
            var c = (SkeletonStatement)cur;
            var S = c.S;
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
                      reporter.Error(MessageSource.RefinementTransformer, c.NameReplacements[k], "replacement definition must contain at most one definition for a given label");
                    } else subExprs.Add(c.NameReplacements[k].val, c.ExprReplacements[k]);
                  }
                  subber = new SubstitutionCloner(subExprs, rawCloner);
                }
                // skip up until the next thing that matches "nxt"
                var hoverTextA = "";
                var sepA = "";
                while (nxt == null || !PotentialMatch(nxt, oldS)) {
                  // loop invariant:  oldS == oldStmt.Body[j]
                  var s = refinementCloner.CloneStmt(oldS);
                  if (subber != null)
                    s = subber.CloneStmt(s);
                  body.Add(s);
                  hoverTextA += sepA + Printer.StatementToString(s);
                  sepA = "\n";
                  j++;
                  if (j == oldStmt.Body.Count) { break; }
                  oldS = oldStmt.Body[j];
                }
                if (hoverTextA.Length != 0) {
                  reporter.Info(MessageSource.RefinementTransformer, c.Tok, hoverTextA);
                }
                if (subber != null && subber.SubstitutionsMade.Count < subber.Exprs.Count) {
                  foreach (var s in subber.SubstitutionsMade)
                    subber.Exprs.Remove(s);
                  reporter.Error(MessageSource.RefinementTransformer, c.Tok, "could not find labeled expression(s): " + Util.Comma(", ", subber.Exprs.Keys, x => x));
                }
              }
              i++;

            } else if (S is AssertStmt) {
              var skel = (AssertStmt)S;
              Contract.Assert(c.ConditionOmitted);
              var oldAssume = oldS as PredicateStmt;
              if (oldAssume == null) {
                reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "assert template does not match inherited statement");
                i++;
              } else {
                // Clone the expression, but among the new assert's attributes, indicate
                // that this assertion is supposed to be translated into a check.  That is,
                // it is not allowed to be just assumed in the translation, despite the fact
                // that the condition is inherited.
                var e = refinementCloner.CloneExpr(oldAssume.Expr);
                var attrs = refinementCloner.MergeAttributes(oldAssume.Attributes, skel.Attributes);
                body.Add(new AssertStmt(new Translator.ForceCheckToken(skel.Tok), new Translator.ForceCheckToken(skel.EndTok),
                  e, new Attributes("prependAssertToken", new List<Expression>(), attrs)));
                reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, "assume->assert: " + Printer.ExprToString(e));
                i++; j++;
              }

            } else if (S is AssumeStmt) {
              var skel = (AssumeStmt)S;
              Contract.Assert(c.ConditionOmitted);
              var oldAssume = oldS as AssumeStmt;
              if (oldAssume == null) {
                reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "assume template does not match inherited statement");
                i++;
              } else {
                var e = refinementCloner.CloneExpr(oldAssume.Expr);
                var attrs = refinementCloner.MergeAttributes(oldAssume.Attributes, skel.Attributes);
                body.Add(new AssumeStmt(skel.Tok, skel.EndTok, e, attrs));
                reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.ExprToString(e));
                i++; j++;
              }

            } else if (S is IfStmt) {
              var skel = (IfStmt)S;
              Contract.Assert(c.ConditionOmitted);
              var oldIf = oldS as IfStmt;
              if (oldIf == null) {
                reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "if-statement template does not match inherited statement");
                i++;
              } else {
                var resultingThen = MergeBlockStmt(skel.Thn, oldIf.Thn);
                var resultingElse = MergeElse(skel.Els, oldIf.Els);
                var e = refinementCloner.CloneExpr(oldIf.Guard);
                var r = new IfStmt(skel.Tok, skel.EndTok, oldIf.IsExistentialGuard, e, resultingThen, resultingElse);
                body.Add(r);
                reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.GuardToString(oldIf.IsExistentialGuard, e));
                i++; j++;
              }

            } else if (S is WhileStmt) {
              var skel = (WhileStmt)S;
              var oldWhile = oldS as WhileStmt;
              if (oldWhile == null) {
                reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "while-statement template does not match inherited statement");
                i++;
              } else {
                Expression guard;
                if (c.ConditionOmitted) {
                  guard = refinementCloner.CloneExpr(oldWhile.Guard);
                  reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.GuardToString(false, oldWhile.Guard));
                } else {
                  if (oldWhile.Guard != null) {
                    reporter.Error(MessageSource.RefinementTransformer, skel.Guard.tok, "a skeleton while statement with a guard can only replace a while statement with a non-deterministic guard");
                  }
                  guard = skel.Guard;
                }
                // Note, if the loop body is omitted in the skeleton, the parser will have set the loop body to an empty block,
                // which has the same merging behavior.
                var r = MergeWhileStmt(skel, oldWhile, guard);
                body.Add(r);
                i++; j++;
              }

            } else if (S is ModifyStmt) {
              var skel = (ModifyStmt)S;
              Contract.Assert(c.ConditionOmitted);
              var oldModifyStmt = oldS as ModifyStmt;
              if (oldModifyStmt == null) {
                reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "modify template does not match inherited statement");
                i++;
              } else {
                var mod = refinementCloner.CloneSpecFrameExpr(oldModifyStmt.Mod);
                BlockStmt mbody;
                if (oldModifyStmt.Body == null && skel.Body == null) {
                  mbody = null;
                } else if (oldModifyStmt.Body == null) {
                  mbody = skel.Body;
                } else if (skel.Body == null) {
                  reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "modify template must have a body if the inherited modify statement does");
                  mbody = null;
                } else {
                  mbody = MergeBlockStmt(skel.Body, oldModifyStmt.Body);
                }
                body.Add(new ModifyStmt(skel.Tok, skel.EndTok, mod.Expressions, mod.Attributes, mbody));
                reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.FrameExprListToString(mod.Expressions));
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
              if (LocalVarsAgree(cOld.Locals, cNew.Locals)) {
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
                var tok = new Translator.ForceCheckToken(addedAssert.tok);
                body.Add(new AssertStmt(tok, tok, addedAssert, null));
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
            if (cOld != null && cNew.Lhs.WasResolved() && cOld.Lhs.WasResolved()) {
              var newLhs = cNew.Lhs.Resolved as IdentifierExpr;
              var oldLhs = cOld.Lhs.Resolved as IdentifierExpr;
              if (newLhs != null && oldLhs != null && newLhs.Name == oldLhs.Name) {
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
                var tok = new Translator.ForceCheckToken(addedAssert.tok);
                stmtGenerated.Add(new AssertStmt(tok, tok, addedAssert, null));
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
              var r = new IfStmt(cNew.Tok, cNew.EndTok, cNew.IsExistentialGuard, cNew.Guard, MergeBlockStmt(cNew.Thn, cOld.Thn), MergeElse(cNew.Els, cOld.Els));
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
      var hoverText = "";
      var sep = "";
      for (; j < oldStmt.Body.Count; j++) {
        var b = oldStmt.Body[j];
        body.Add(refinementCloner.CloneStmt(b));
        hoverText += sep + Printer.StatementToString(b);
        sep = "\n";
      }
      if (hoverText.Length != 0) {
        reporter.Info(MessageSource.RefinementTransformer, skeleton.EndTok, hoverText);
      }
      return new BlockStmt(skeleton.Tok, skeleton.EndTok, body);
    }

    private bool LeftHandSidesAgree(List<Expression> old, List<Expression> nw) {
      if (old.Count != nw.Count)
        return false;
      for (int i = 0; i < old.Count; i++) {
        var a = old[i].WasResolved() ? old[i].Resolved as IdentifierExpr : null;
        var b = nw[i] as NameSegment;
        if (a != null && b != null && a.Name == b.Name) {
          // cool
        } else {
          return false;
        }
      }
      return true;
    }
    private bool LocalVarsAgree(List<LocalVariable> old, List<LocalVariable> nw) {
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
        } else if (S is ModifyStmt) {
          return other is ModifyStmt;
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
        return oth != null && LocalVarsAgree(((VarDeclStmt)nxt).Locals, oth.Locals);
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

      Specification<Expression> decr;
      if (cNew.Decreases.Expressions.Count == 0) {
        // inherited whatever the previous loop used
        decr = refinementCloner.CloneSpecExpr(cOld.Decreases);
      } else {
        if (!Contract.Exists(cOld.Decreases.Expressions, e => e is WildcardExpr)) {
          // If the previous loop was not specified with "decreases *", then the new loop is not allowed to provide any "decreases" clause.
          reporter.Error(MessageSource.RefinementTransformer, cNew.Decreases.Expressions[0].tok, "a refining loop can provide a decreases clause only if the loop being refined was declared with 'decreases *'");
        }
        decr = cNew.Decreases;
      }

      var invs = cOld.Invariants.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
      invs.AddRange(cNew.Invariants);
      var r = new RefinedWhileStmt(cNew.Tok, cNew.EndTok, guard, invs, decr, refinementCloner.CloneSpecFrameExpr(cOld.Mod), MergeBlockStmt(cNew.Body, cOld.Body));
      return r;
    }

    Statement MergeElse(Statement skeleton, Statement oldStmt) {
      Contract.Requires(skeleton == null || skeleton is BlockStmt || skeleton is IfStmt || skeleton is SkeletonStatement);
      Contract.Requires(oldStmt == null || oldStmt is BlockStmt || oldStmt is IfStmt || oldStmt is SkeletonStatement);

      if (skeleton == null) {
        return refinementCloner.CloneStmt(oldStmt);
      } else if (skeleton is IfStmt || skeleton is SkeletonStatement) {
        // wrap a block statement around the if statement
        skeleton = new BlockStmt(skeleton.Tok, skeleton.EndTok, new List<Statement>() { skeleton });
      }

      if (oldStmt == null) {
        // make it into an empty block statement
        oldStmt = new BlockStmt(skeleton.Tok, skeleton.EndTok, new List<Statement>());
      } else if (oldStmt is IfStmt || oldStmt is SkeletonStatement) {
        // wrap a block statement around the if statement
        oldStmt = new BlockStmt(oldStmt.Tok, skeleton.EndTok, new List<Statement>() { oldStmt });
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
      var prevErrorCount = reporter.Count(ErrorLevel.Error);
      CheckIsOkayNewStatement(s, new Stack<string>(), 0);
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
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
        reporter.Error(MessageSource.RefinementTransformer, s, "skeleton statement may not be used here; it does not have a matching statement in what is being replaced");
      } else if (s is ReturnStmt) {
        // allow return statements, but make note of that this requires verifying the postcondition
        ((ReturnStmt)s).ReverifyPost = true;
      } else if (s is YieldStmt) {
        reporter.Error(MessageSource.RefinementTransformer, s, "yield statements are not allowed in skeletons");
      } else if (s is BreakStmt) {
        var b = (BreakStmt)s;
        if (b.TargetLabel != null ? !labels.Contains(b.TargetLabel) : loopLevels < b.BreakCount) {
          reporter.Error(MessageSource.RefinementTransformer, s, "break statement in skeleton is not allowed to break outside the skeleton fragment");
        }
      } else if (s is AssignStmt) {
        // TODO: To be a refinement automatically (that is, without any further verification), only variables and fields defined
        // in this module are allowed.  This needs to be checked.  If the LHS refers to an l-value that was not declared within
        // this module, then either an error should be reported or the Translator needs to know to translate new proof obligations.
        var a = (AssignStmt)s;
        reporter.Error(MessageSource.RefinementTransformer, a.Tok, "cannot have assignment statement");
      } else if (s is ConcreteUpdateStatement) {
        postTasks.Enqueue(() =>
        {
          CheckIsOkayUpdateStmt((ConcreteUpdateStatement)s, moduleUnderConstruction);
        });
      } else if (s is CallStmt) {
        reporter.Error(MessageSource.RefinementTransformer, s.Tok, "cannot have call statement");
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
    void CheckIsOkayUpdateStmt(ConcreteUpdateStatement stmt, ModuleDefinition m) {
      foreach (var lhs in stmt.Lhss) {
        var l = lhs.Resolved;
        if (l is IdentifierExpr) {
          var ident = (IdentifierExpr)l;
          Contract.Assert(ident.Var is LocalVariable || ident.Var is Formal); // LHS identifier expressions must be locals or out parameters (ie. formals)
          if ((ident.Var is LocalVariable && RefinementToken.IsInherited(((LocalVariable)ident.Var).Tok, m)) || ident.Var is Formal) {
            // for some reason, formals are not considered to be inherited.
            reporter.Error(MessageSource.RefinementTransformer, l.tok, "refinement method cannot assign to variable defined in parent module ('{0}')", ident.Var.Name);
          }
        } else if (l is MemberSelectExpr) {
          var member = ((MemberSelectExpr)l).Member;
          if (RefinementToken.IsInherited(member.tok, m)) {
            reporter.Error(MessageSource.RefinementTransformer, l.tok, "refinement method cannot assign to a field defined in parent module ('{0}')", member.Name);
          }
        } else {
          // must be an array element
          reporter.Error(MessageSource.RefinementTransformer, l.tok, "new assignments in a refinement method can only assign to state that the module defines (which never includes array elements)");
        }
      }
      if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var rhs in s.Rhss) {
          if (rhs.CanAffectPreviouslyKnownExpressions) {
            reporter.Error(MessageSource.RefinementTransformer, rhs.Tok, "assignment RHS in refinement method is not allowed to affect previously defined state");
          }
        }
      }
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
        return new Attributes(moreAttrs.Name, moreAttrs.Args.ConvertAll(CloneExpr), MergeAttributes(prevAttrs, moreAttrs.Prev));
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