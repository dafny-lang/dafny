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
    RefinementCloner refinementCloner; // This cloner wraps things in a RefinementToken

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
    private ModuleSignature refinedSigOpened;

    internal override void PreResolve(ModuleDefinition m) {
      if (m.RefinementBaseRoot != null) {
        RefinedSig = m.RefinementBaseRoot.Signature;

        if (RefinedSig.ModuleDef != null) {
          if (RefinedSig.ModuleDef.IsProtected) {
            reporter.Error(MessageSource.RefinementTransformer, m.RefinementBaseName, "module ({0}) named as a refinement base is marked protected and cannot be refined", m.RefinementBaseName.val);
          }

          m.RefinementBase = RefinedSig.ModuleDef;
          // check that the openess in the imports between refinement and its base matches
          List<TopLevelDecl> declarations = m.TopLevelDecls;
          List<TopLevelDecl> baseDeclarations = m.RefinementBase.TopLevelDecls;
          foreach (var im in declarations) {
            if (im is ModuleDecl) {
              ModuleDecl mdecl = (ModuleDecl)im;
              //find the matching import from the base
              // TODO: this is a terribly slow algorithm; use the symbol table instead
              foreach (var bim in baseDeclarations) {
                if (bim is ModuleDecl && ((ModuleDecl)bim).Name.Equals(mdecl.Name)) {
                  if (mdecl.Opened != ((ModuleDecl)bim).Opened) {
                    string message = mdecl.Opened ?
                      "{0} in {1} cannot be imported with \"opened\" because it does not match the corresponding import in the refinement base {2} " :
                      "{0} in {1} must be imported with \"opened\"  to match the corresponding import in its refinement base {2}.";
                    reporter.Error(MessageSource.RefinementTransformer, m.tok, message, im.Name, m.Name, m.RefinementBase.Name);
                  }
                  break;
                }
                break;
              }
            }
          }
          PreResolveWorker(m);

        } else {
          reporter.Error(MessageSource.RefinementTransformer, m.RefinementBaseName, "module ({0}) named as refinement base does not exist", m.RefinementBaseName.val);
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

      //copy the signature, including its opened imports
      refinedSigOpened = Resolver.MergeSignature(new ModuleSignature(), RefinedSig);
      Resolver.ResolveOpenedImports(refinedSigOpened, m.RefinementBase, false, null);

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < m.TopLevelDecls.Count; i++) {
        var d = m.TopLevelDecls[i];
        if (!declaredNames.ContainsKey(d.Name)) {
          declaredNames.Add(d.Name, i);
        }

        // TODO: This is more restrictive than is necessary,
        // it would be possible to disambiguate these, but it seems like
        // a lot of work for not much gain

        if (refinedSigOpened.TopLevels.ContainsKey(d.Name) &&
          !RefinedSig.TopLevels.ContainsKey(d.Name)) {
          var decl = Resolver.AmbiguousTopLevelDecl.Create(m, d, refinedSigOpened.TopLevels[d.Name]);

          if (decl is Resolver.AmbiguousTopLevelDecl) {
            reporter.Error(MessageSource.RefinementTransformer, d.tok, "Base module {0} imports {1} from an opened import, so it cannot be overridden. Give this declaration a unique name to disambiguate.", prev.Name, d.Name);
          }
        }
      }

      // Merge the declarations of prev into the declarations of m
      List<string> processedDecl = new List<string>();
      foreach (var d in prev.TopLevelDecls) {
        int index;
        processedDecl.Add(d.Name);
        if (!declaredNames.TryGetValue(d.Name, out index)) {
          m.TopLevelDecls.Add(refinementCloner.CloneDeclaration(d, m));
        } else {
          var nw = m.TopLevelDecls[index];
          MergeTopLevelDecls(m, nw, d, index);
        }
      }

      // Merge the imports of prev
      var prevTopLevelDecls = RefinedSig.TopLevels.Values;
      foreach (var d in prevTopLevelDecls) {
        int index;
        if (!processedDecl.Contains(d.Name) && (declaredNames.TryGetValue(d.Name, out index))) {
          // if it is redefined, we need to merge them.
          var nw = m.TopLevelDecls[index];
          MergeTopLevelDecls(m, nw, d, index);
        }
      }
      m.RefinementBaseSig = RefinedSig;

      Contract.Assert(moduleUnderConstruction == m);  // this should be as it was set earlier in this method
    }

    private void MergeModuleExports(ModuleExportDecl nw, ModuleExportDecl d) {
      if (nw.IsDefault != d.IsDefault) {
        reporter.Error(MessageSource.RefinementTransformer, nw, "can't change if a module export is default ({0})", nw.Name);
      }

      nw.Exports.AddRange(d.Exports);
      nw.Extends.AddRange(d.Extends);
    }

    private void MergeTopLevelDecls(ModuleDefinition m, TopLevelDecl nw, TopLevelDecl d, int index) {
      if (d is ModuleDecl) {
        if (!(nw is ModuleDecl)) {
          reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
        } else if (d is ModuleExportDecl) {
          if (!(nw is ModuleExportDecl)) {
            reporter.Error(MessageSource.RefinementTransformer, nw, "a module export ({0}) must refine another export", nw.Name);
          } else {
            MergeModuleExports((ModuleExportDecl)nw,(ModuleExportDecl)d);
          }
        } else if (!(d is ModuleFacadeDecl)) {
          reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) can only refine a module facade", nw.Name);
        } else {
          // check that the new module refines the previous declaration
          if (!CheckIsRefinement((ModuleDecl)nw, (ModuleFacadeDecl)d))
            reporter.Error(MessageSource.RefinementTransformer, nw.tok, "a module ({0}) can only be replaced by a refinement of the original module", d.Name);
        }
      } else if (d is OpaqueTypeDecl) {
        if (nw is ModuleDecl) {
          reporter.Error(MessageSource.RefinementTransformer, nw, "a module ({0}) must refine another module", nw.Name);
        } else {
          var od = (OpaqueTypeDecl)d;
          if (nw is OpaqueTypeDecl) {
            if (od.MustSupportEquality != ((OpaqueTypeDecl)nw).MustSupportEquality) {
              reporter.Error(MessageSource.RefinementTransformer, nw, "type declaration '{0}' is not allowed to change the requirement of supporting equality", nw.Name);
            }
            if (od.Characteristics.MustSupportZeroInitialization != ((OpaqueTypeDecl)nw).Characteristics.MustSupportZeroInitialization) {
              reporter.Error(MessageSource.RefinementTransformer, nw.tok, "type declaration '{0}' is not allowed to change the requirement of supporting zero initialization", nw.Name);
            }
          } else {
            if (od.MustSupportEquality) {
              if (nw is ClassDecl || nw is NewtypeDecl) {
                // fine
              } else if (nw is CoDatatypeDecl) {
                reporter.Error(MessageSource.RefinementTransformer, nw, "a type declaration that requires equality support cannot be replaced by a codatatype");
              } else {
                Contract.Assert(nw is IndDatatypeDecl || nw is TypeSynonymDecl);
                // Here, we need to figure out if the new type supports equality.  But we won't know about that until resolution has
                // taken place, so we defer it until the PostResolve phase.
                var udt = UserDefinedType.FromTopLevelDecl(nw.tok, nw);
                postTasks.Enqueue(() => {
                  if (!udt.SupportsEquality) {
                    reporter.Error(MessageSource.RefinementTransformer, udt.tok, "type '{0}', which does not support equality, is used to refine an opaque type with equality support", udt.Name);
                  }
                });
              }
            }
            if (od.Characteristics.MustSupportZeroInitialization) {
              // We need to figure out if the new type supports zero initialization.  But we won't know about that until resolution has
              // taken place, so we defer it until the PostResolve phase.
              var udt = UserDefinedType.FromTopLevelDecl(nw.tok, nw);
              postTasks.Enqueue(() => {
                if (!Compiler.HasZeroInitializer(udt)) {
                  reporter.Error(MessageSource.RefinementTransformer, udt.tok, "type '{0}', which does not support zero initialization, is used to refine an opaque type that expects zero initialization", udt.Name);
                }
              });
            }
          }
          CheckAgreement_TypeParameters(nw.tok, d.TypeArgs, nw.TypeArgs, nw.Name, "type", false);
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

    public bool CheckIsRefinement(ModuleDecl derived, ModuleFacadeDecl original) {


      // Check explicit refinement
      // TODO syntactic analysis of export sets is not quite right
      var derivedPointer = derived.Signature.ModuleDef;
      while (derivedPointer != null) {
        if (derivedPointer == original.OriginalSignature.ModuleDef) {
          HashSet<string> exports;
          if (derived is AliasModuleDecl) {
            exports = new HashSet<string>(((AliasModuleDecl)derived).Exports.ConvertAll(t => t.val));
          } else if (derived is ModuleFacadeDecl) {
            exports = new HashSet<string>(((ModuleFacadeDecl)derived).Exports.ConvertAll(t => t.val));
          } else {
            reporter.Error(MessageSource.RefinementTransformer, derived, "a module ({0}) can only be refined by an alias module or a module facade", original.Name);
            return false;
          }
          var oexports = new HashSet<string>(original.Exports.ConvertAll(t => t.val));
          return oexports.IsSubsetOf(exports);
        }
        derivedPointer = derivedPointer.RefinementBase;
      }
      return false;
    }

    // Check that two resolved types are the same in a similar context (the same type parameters, method, class, etc.)
    // Assumes that prev is in a previous refinement, and next is in some refinement. Note this is not commutative.
    public bool ResolvedTypesAreTheSame(Type prev, Type next) {
      Contract.Requires(prev != null);
      Contract.Requires(next != null);

      prev = prev.NormalizeExpandKeepConstraints();
      next = next.NormalizeExpandKeepConstraints();

      if (prev is TypeProxy || next is TypeProxy)
        return false;

      if (prev is BoolType) {
        return next is BoolType;
      } else if (prev is CharType) {
        return next is CharType;
      } else if (prev is IntType) {
        return next is IntType;
      } else if (prev is RealType) {
        return next is RealType;
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
        if (aa.ResolvedClass != null && bb.ResolvedClass != null && aa.ResolvedClass == bb.ResolvedClass) {
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
        } else if (aa.ResolvedParam != null && aa.ResolvedParam.IsAbstractTypeDeclaration && bb.ResolvedClass != null) {
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

    Function CloneFunction(IToken tok, Function f, bool isGhost, List<MaybeFreeExpression> moreEnsures, Formal moreResult, Expression moreBody, Expression replacementBody, bool checkPrevPostconditions, Attributes moreAttributes) {
      Contract.Requires(tok != null);
      Contract.Requires(moreBody == null || f is Predicate);
      Contract.Requires(moreBody == null || replacementBody == null);

      var tps = f.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam);
      var formals = f.Formals.ConvertAll(refinementCloner.CloneFormal);
      var req = f.Req.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
      var reads = f.Reads.ConvertAll(refinementCloner.CloneFrameExpr);
      var decreases = refinementCloner.CloneSpecExpr(f.Decreases);
      var result = f.Result ?? moreResult;
      if (result != null) {
        result = refinementCloner.CloneFormal(result);
      }

      List<MaybeFreeExpression> ens;
      if (checkPrevPostconditions)  // note, if a postcondition includes something that changes in the module, the translator will notice this and still re-check the postcondition
        ens = f.Ens.ConvertAll(rawCloner.CloneMayBeFreeExpr);
      else
        ens = f.Ens.ConvertAll(refinementCloner.CloneMayBeFreeExpr);
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
          req, reads, ens, decreases, body, bodyOrigin, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      } else if (f is InductivePredicate) {
        return new InductivePredicate(tok, f.Name, f.HasStaticKeyword, f.IsProtected, ((InductivePredicate)f).TypeOfK, tps, formals,
          req, reads, ens, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      } else if (f is CoPredicate) {
        return new CoPredicate(tok, f.Name, f.HasStaticKeyword, f.IsProtected, ((CoPredicate)f).TypeOfK, tps, formals,
          req, reads, ens, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      } else if (f is TwoStatePredicate) {
        return new TwoStatePredicate(tok, f.Name, f.HasStaticKeyword, tps, formals,
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      } else if (f is TwoStateFunction) {
        return new TwoStateFunction(tok, f.Name, f.HasStaticKeyword, tps, formals, result, refinementCloner.CloneType(f.ResultType),
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      } else {
        return new Function(tok, f.Name, f.HasStaticKeyword, f.IsProtected, isGhost, tps, formals, result, refinementCloner.CloneType(f.ResultType),
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(f.Attributes, moreAttributes), null);
      }
    }

    Method CloneMethod(Method m, List<MaybeFreeExpression> moreEnsures, Specification<Expression> decreases, BlockStmt newBody, bool checkPreviousPostconditions, Attributes moreAttributes) {
      Contract.Requires(m != null);
      Contract.Requires(!(m is Constructor) || newBody == null || newBody is DividedBlockStmt);
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

      if (m is Constructor) {
        var dividedBody = (DividedBlockStmt)newBody ?? refinementCloner.CloneDividedBlockStmt((DividedBlockStmt)m.BodyForRefinement);
        return new Constructor(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, tps, ins,
          req, mod, ens, decreases, dividedBody, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
      }
      var body = newBody ?? refinementCloner.CloneBlockStmt(m.BodyForRefinement);
      if (m is InductiveLemma) {
        return new InductiveLemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, ((InductiveLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
      } else if (m is CoLemma) {
        return new CoLemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, ((CoLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
      } else if (m is Lemma) {
        return new Lemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
      } else if (m is TwoStateLemma) {
        var two = (TwoStateLemma)m;
        return new TwoStateLemma(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
      } else {
        return new Method(new RefinementToken(m.tok, moduleUnderConstruction), m.Name, m.HasStaticKeyword, m.IsGhost, tps, ins, m.Outs.ConvertAll(refinementCloner.CloneFormal),
          req, mod, ens, decreases, body, refinementCloner.MergeAttributes(m.Attributes, moreAttributes), null);
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

        if (prev.IsDefaultClass && refinedSigOpened.StaticMembers.ContainsKey(member.Name) &&
          !RefinedSig.StaticMembers.ContainsKey(member.Name)) {
            reporter.Error(MessageSource.RefinementTransformer, member.tok, "Base module {0} imports {1} from an opened import, so it cannot be overridden. Give this declaration a unique name to disambiguate.", RefinedSig.ModuleDef.Name, member.Name);
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
          if (nwMember is ConstantField) {
            var newConst = (ConstantField)nwMember;
            var origConst = member as ConstantField;
            if (origConst == null) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a const declaration ({0}) in a refining class ({1}) must replace a const in the refinement base", nwMember.Name, nw.Name);
            } else if (!(newConst.Type is InferredTypeProxy) && !TypesAreSyntacticallyEqual(newConst.Type, origConst.Type)) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "the type of a const declaration ({0}) in a refining class ({1}) must be syntactically the same as for the const being refined", nwMember.Name, nw.Name);
            } else if (newConst.Rhs != null && origConst.Rhs != null) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a const re-declaration ({0}) can give an initializing expression only if the const in the refinement base does not", nwMember.Name);
            } else if (newConst.HasStaticKeyword != origConst.HasStaticKeyword) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a const in a refining module cannot be changed from static to non-static or vice versa: {0}", nwMember.Name);
            } else if (origConst.IsGhost && !newConst.IsGhost) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a const re-declaration ({0}) is not allowed to un-ghostify the const", nwMember.Name);
            } else if (newConst.Rhs == null && origConst.IsGhost == newConst.IsGhost) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a const re-declaration ({0}) must be to ghostify the const{1}", nwMember.Name, origConst.Rhs == null ? " or to provide an initializing expression" : "");
            }
            nwMember.RefinementBase = member;
            // we may need to clone the given const declaration if either its type or initializing expression was omitted
            if (origConst != null) {
              if ((!(origConst.Type is InferredTypeProxy) && newConst.Type is InferredTypeProxy) || (origConst.Rhs != null && newConst.Rhs == null)) {
                var typ = newConst.Type is InferredTypeProxy ? refinementCloner.CloneType(origConst.Type) : newConst.Type;
                var rhs = newConst.Rhs ?? origConst.Rhs;
                nw.Members[index] = new ConstantField(newConst.tok, newConst.Name, rhs, newConst.HasStaticKeyword, newConst.IsGhost, typ, newConst.Attributes);
              }
            }

          } else if (nwMember is Field) {
            if (!(member is Field) || member is ConstantField) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a field declaration ({0}) in a refining class ({1}) must replace a field in the refinement base", nwMember.Name, nw.Name);
            } else if (!TypesAreSyntacticallyEqual(((Field)nwMember).Type, ((Field)member).Type)) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a field declaration ({0}) in a refining class ({1}) must repeat the syntactically same type as the field has in the refinement base", nwMember.Name, nw.Name);
            } else if (member.IsGhost || !nwMember.IsGhost) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a field re-declaration ({0}) must be to ghostify the field", nwMember.Name);
            }
            nwMember.RefinementBase = member;

          } else if (nwMember is Function) {
            var f = (Function)nwMember;
            bool isPredicate = f is Predicate;
            bool isIndPredicate = f is InductivePredicate;
            bool isCoPredicate = f is CoPredicate;
            if (!(member is Function) ||
              isPredicate != (member is Predicate) ||
              (f is InductivePredicate) != (member is InductivePredicate) ||
              (f is CoPredicate) != (member is CoPredicate) ||
              (f is TwoStatePredicate) != (member is TwoStatePredicate) ||
              (f is TwoStateFunction) != (member is TwoStateFunction)) {
              reporter.Error(MessageSource.RefinementTransformer, nwMember, "a {0} declaration ({1}) can only refine a {0}", f.WhatKind, nwMember.Name);
            } else if (f.IsProtected != ((Function)member).IsProtected) {
              reporter.Error(MessageSource.RefinementTransformer, f, "a {0} in a refinement module must be declared 'protected' if and only if the refined {0} is", f.WhatKind);
            } else {
              var prevFunction = (Function)member;
              if (f.Req.Count != 0) {
                reporter.Error(MessageSource.RefinementTransformer, f.Req[0].E.tok, "a refining {0} is not allowed to add preconditions", f.WhatKind);
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
                if (prevFunction.Result != null && f.Result != null && prevFunction.Result.Name != f.Result.Name) {
                  reporter.Error(MessageSource.RefinementTransformer, f, "the name of function return value '{0}'({1}) differs from the name of corresponding function return value in the module it refines ({2})", f.Name, f.Result.Name, prevFunction.Result.Name);
                }
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
              var newF = CloneFunction(f.tok, prevFunction, f.IsGhost, f.Ens, f.Result, moreBody, replacementBody, prevFunction.Body == null, f.Attributes);
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
              var replacementBody = m.BodyForRefinement;
              if (replacementBody != null) {
                if (prevMethod.BodyForRefinement == null) {
                  // cool
                } else {
                  replacementBody = MergeBlockStmt(replacementBody, prevMethod.BodyForRefinement);
                }
              }
              var newM = CloneMethod(prevMethod, m.Ens, decreases, replacementBody, prevMethod.BodyForRefinement == null, m.Attributes);
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
            if (o.Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired && o.Characteristics.EqualitySupport != n.Characteristics.EqualitySupport) {
              reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
            }
            if (o.Characteristics.MustSupportZeroInitialization != n.Characteristics.MustSupportZeroInitialization) {
              reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting zero initialization", n.Name);
            }
            if (o.Characteristics.DisallowReferenceTypes != n.Characteristics.DisallowReferenceTypes) {
              reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the no-reference-type requirement", n.Name);
            }
            if (o.Variance != n.Variance) {  // syntax is allowed to be different as long as the meaning is the same (i.e., compare Variance, not VarianceSyntax)
              var ov = o.Variance == TypeParameter.TPVariance.Co ? "+" : o.Variance == TypeParameter.TPVariance.Contra ? "-" : "=";
              var nv = n.Variance == TypeParameter.TPVariance.Co ? "+" : n.Variance == TypeParameter.TPVariance.Contra ? "-" : "=";
              reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change variance (here, from '{1}' to '{2}')", n.Name, ov, nv);
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
                    if (o.Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired && o.Characteristics.EqualitySupport != n.Characteristics.EqualitySupport)
                    {
                        reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
                    }
                    if (o.Characteristics.MustSupportZeroInitialization != n.Characteristics.MustSupportZeroInitialization) {
                      reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting zero initialization", n.Name);
                    }
                    if (o.Characteristics.DisallowReferenceTypes != n.Characteristics.DisallowReferenceTypes) {
                      reporter.Error(MessageSource.RefinementTransformer, n.tok, "type parameter '{0}' is not allowed to change the no-reference-type requirement", n.Name);
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
                if (!o.IsGhost && n.IsGhost) {
                  reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from non-ghost to ghost", parameterKind, n.Name, thing, name);
                } else if (o.IsGhost && !n.IsGhost) {
                  reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from ghost to non-ghost", parameterKind, n.Name, thing, name);
                } else if (!o.IsOld && n.IsOld) {
                  reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from non-new to new", parameterKind, n.Name, thing, name);
                } else if (o.IsOld && !n.IsOld) {
                  reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it overrides, from new to non-new", parameterKind, n.Name, thing, name);
                } else if (!ResolvedTypesAreTheSame(o.Type, n.Type)) {
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
          } else if (!o.IsOld && n.IsOld) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-new to new", parameterKind, n.Name, thing, name);
          } else if (o.IsOld && !n.IsOld) {
            reporter.Error(MessageSource.RefinementTransformer, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from new to non-new", parameterKind, n.Name, thing, name);
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
      Contract.Requires(skeleton is DividedBlockStmt == oldStmt is DividedBlockStmt);

      if (skeleton is DividedBlockStmt) {
        var sbsSkeleton = (DividedBlockStmt)skeleton;
        var sbsOldStmt = (DividedBlockStmt)oldStmt;
        string hoverText;
        var bodyInit = MergeStmtList(sbsSkeleton.BodyInit, sbsOldStmt.BodyInit, out hoverText);
        if (hoverText.Length != 0) {
          reporter.Info(MessageSource.RefinementTransformer, sbsSkeleton.SeparatorTok ?? sbsSkeleton.Tok, hoverText);
        }
        var bodyProper = MergeStmtList(sbsSkeleton.BodyProper, sbsOldStmt.BodyProper, out hoverText);
        if (hoverText.Length != 0) {
          reporter.Info(MessageSource.RefinementTransformer, sbsSkeleton.EndTok, hoverText);
        }
        return new DividedBlockStmt(sbsSkeleton.Tok, sbsSkeleton.EndTok, bodyInit, sbsSkeleton.SeparatorTok, bodyProper);
      } else {
        string hoverText;
        var body = MergeStmtList(skeleton.Body, oldStmt.Body, out hoverText);
        if (hoverText.Length != 0) {
          reporter.Info(MessageSource.RefinementTransformer, skeleton.EndTok, hoverText);
        }
        return new BlockStmt(skeleton.Tok, skeleton.EndTok, body);
      }
    }

    List<Statement> MergeStmtList(List<Statement> skeleton, List<Statement> oldStmt, out string hoverText) {
      Contract.Requires(skeleton != null);
      Contract.Requires(oldStmt != null);
      Contract.Ensures(Contract.ValueAtReturn(out hoverText) != null);
      Contract.Ensures(Contract.Result<List<Statement>>() != null);

      hoverText = "";
      var body = new List<Statement>();
      int i = 0, j = 0;
      while (i < skeleton.Count) {
        var cur = skeleton[i];
        if (j == oldStmt.Count) {
          if (!(cur is SkeletonStatement)) {
            MergeAddStatement(cur, body);
          } else if (((SkeletonStatement)cur).S == null) {
            // the "..." matches the empty statement sequence
          } else {
            reporter.Error(MessageSource.RefinementTransformer, cur.Tok, "skeleton statement does not match old statement");
          }
          i++;
        } else {
          var oldS = oldStmt[j];
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
              var nxt = i + 1 == skeleton.Count ? null : skeleton[i + 1];
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
                  if (j == oldStmt.Count) { break; }
                  oldS = oldStmt[j];
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
                  e, skel.Proof, skel.Label, new Attributes("_prependAssertToken", new List<Expression>(), attrs)));
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
                var r = new IfStmt(skel.Tok, skel.EndTok, oldIf.IsBindingGuard, e, resultingThen, resultingElse);
                body.Add(r);
                reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.GuardToString(oldIf.IsBindingGuard, e));
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
                body.Add(new AssertStmt(tok, tok, addedAssert, null, null, null));
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
                stmtGenerated.Add(new AssertStmt(tok, tok, addedAssert, null, null, null));
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
              var r = new IfStmt(cNew.Tok, cNew.EndTok, cNew.IsBindingGuard, cNew.Guard, MergeBlockStmt(cNew.Thn, cOld.Thn), MergeElse(cNew.Els, cOld.Els));
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
      var sep = "";
      for (; j < oldStmt.Count; j++) {
        var b = oldStmt[j];
        body.Add(refinementCloner.CloneStmt(b));
        hoverText += sep + Printer.StatementToString(b);
        sep = "\n";
      }
      return body;
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
    public override BlockStmt CloneMethodBody(Method m) {
      if (m.BodyForRefinement is DividedBlockStmt) {
        return CloneDividedBlockStmt((DividedBlockStmt)m.BodyForRefinement);
      } else {
        return CloneBlockStmt(m.BodyForRefinement);
      }
    }
    public override IToken Tok(IToken tok) {
      return new RefinementToken(tok, moduleUnderConstruction);
    }
    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      var dd = base.CloneDeclaration(d, m);
      if (dd is ModuleExportDecl) {
        ((ModuleExportDecl)dd).SetupDefaultSignature();
      } else if (d is ModuleDecl) {
        ((ModuleDecl)dd).Signature = ((ModuleDecl)d).Signature;
        if (d is ModuleFacadeDecl) {
          ((ModuleFacadeDecl)dd).OriginalSignature = ((ModuleFacadeDecl)d).OriginalSignature;
        }
      }
      return dd;
    }
    public virtual Attributes MergeAttributes(Attributes prevAttrs, Attributes moreAttrs) {
      if (moreAttrs == null) {
        return CloneAttributes(prevAttrs);
      } else if (moreAttrs is UserSuppliedAttributes) {
        var usa = (UserSuppliedAttributes)moreAttrs;
        return new UserSuppliedAttributes(Tok(usa.tok), Tok(usa.OpenBrace), Tok(usa.CloseBrace), moreAttrs.Args.ConvertAll(CloneExpr), MergeAttributes(prevAttrs, moreAttrs.Prev));
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
