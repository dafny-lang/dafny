//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
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
using System.Linq;
using Microsoft.Dafny.Plugins;
using static Microsoft.Dafny.RefinementErrors;

namespace Microsoft.Dafny {
  /// <summary>
  /// The "RefinementTransformer" is responsible for transforming a refining module (that is,
  /// a module defined as "module Y refines X") according to the body of this module and
  /// the module used as a starting point for the refinement (here, "X"). In a nutshell,
  /// there are four kinds of transformations.
  /// 
  ///   0. "Y" can fill in some definitions that "X" omitted. For example, if "X" defines
  ///      an abstract type "type T", then "Y" can define "T" to be a particular type, like
  ///      "type T = int". As another example, if "X" omits the body of a function, then
  ///      "Y" can give it a body.
  /// 
  ///   1. "Y" can add definitions. For example, it can declare new types and it can add
  ///      members to existing types.
  ///  
  ///   2. "Y" can superimpose statements on an existing method body. The format for this
  ///      is something that confuses most people. One reason for the common confusion is
  ///      that in many other language situations, it's the original ("X") that says what
  ///      parts can be replaced. Here, it the refining module ("Y") that decides where to
  ///      "squeeze in" new statements. For example, if a method body in "X" is
  /// 
  ///          var i := 0;
  ///          while i != 10 {
  ///            i := i + 1;
  ///          }
  /// 
  ///      then the refining module can write
  ///
  ///          var j := 0;
  ///          ...;
  ///          while ...
  ///            invariant j == 2 * i
  ///          {
  ///            j := j + 2;
  ///          }
  ///
  ///      Note, the two occurrences of "..." above are concrete syntax in Dafny.
  ///
  ///      In the RefinementTransformer methods below, the former usually goes by some name like
  ///      "oldStmt", whereas the latter has some name like "skeleton". (Again, this can be confusing,
  ///      because a "skeleton" (or "template") is something you *add* things to, whereas here it is
  ///      description for *how* to add something to the "oldStmt".)
  ///
  ///      The result of combining the "oldStmt" and the "skeleton" is called the "Merge" of
  ///      the two. For the example above, the merge is:
  /// 
  ///          var j := 0;
  ///          var i := 0;
  ///          while i != 10
  ///            invariant j == 2 * i
  ///          {
  ///            j := j + 2;
  ///            i := i + 1;
  ///          }
  ///
  ///      The IDE adds hover text that shows what each "...;" or "}" in the "skeleton" expands
  ///      to.
  ///
  ///      Roughly speaking, the new program text that is being superimposed on the old is
  ///      allowed to add local variables and assignments to those (like "j" in the example above).
  ///      It is also allowed to add some forms of assertions (like the "invariant" in the
  ///      example). It cannot add statements that change the control flow, except that it
  ///      is allowed to add "return;" statements. Finally, in addition to these superimpositions,
  ///      there's a small number of refinement changes it can make. For example, it can reduce
  ///      nondeterminism in certain ways; e.g., it can change a statement "r :| 0 <= r <= 100;"
  ///      into "r := 38;". As another example of a refinement, it change change an "assume"
  ///      into an "assert" (by writing "assert ...;").
  ///
  ///      The rules about what kinds of superimpositions the language can allow has as its
  ///      guiding principle the idea that the verifier should not need to reverify anything that
  ///      was already verified in module "X". In some special cases, a superimposition needs
  ///      some condition to be verified (for example, an added "return;" statement causes the
  ///      postcondition to be reverified, but only at the point of the "return;"), so the verifier
  ///      adds the necessary additional checks.
  ///  
  ///   3. Some modifiers and other decorations may be changed. For example, a "ghost var"
  ///      field can be changed to a "var" field, and vice versa. It may seem odd that a
  ///      refinement is allowed to change these (and in either direction!), but it's fine
  ///      as long as it doesn't affect what the verifier does. The entire merged module is
  ///      passed through Resolution, which catches any errors that these small changes
  ///      may bring about. For example, it will give an error for an assignment "a := b;"
  ///      if "a" and "b" were both compiled variables in "X" and "b" has been changed to be
  ///      a ghost variable in "Y".
  ///
  /// For more information about the refinement features in Dafny, see
  ///
  ///      "Programming Language Features for Refinement"
  ///      Jason Koenig and K. Rustan M. Leino.
  ///      In EPTCS, 2016. (Post-workshop proceedings of REFINE 2015.) 
  /// </summary>
  public class RefinementTransformer : IRewriter {
    RefinementCloner refinementCloner; // This cloner wraps things in a RefinementToken

    public RefinementTransformer(ErrorReporter reporter)
      : base(reporter) {
    }

    public RefinementTransformer(Program p)
      : this(p.Reporter) {
    }

    private void Error(ErrorId errorId, IOrigin tok, string msg, params object[] args) {
      Reporter.Error(MessageSource.RefinementTransformer, errorId, tok, msg, args);
    }

    private void Error(ErrorId errorId, Declaration d, string msg, params object[] args) {
      Reporter.Error(MessageSource.RefinementTransformer, errorId, d.Origin, msg, args);
    }

    private void Error(ErrorId errorId, INode n, string msg, params object[] args) {
      Reporter.Error(MessageSource.RefinementTransformer, errorId, n.Origin, msg, args);
    }

    private ModuleDefinition moduleUnderConstruction;  // non-null for the duration of Construct calls
    private Queue<Action> postTasks = new Queue<Action>();  // empty whenever moduleUnderConstruction==null, these tasks are for the post-resolve phase of module moduleUnderConstruction
    public Queue<Tuple<MethodOrConstructor, MethodOrConstructor>> translationMethodChecks = new();  // contains all the methods that need to be checked for structural refinement.
    private MethodOrConstructor currentMethod;
    private ModuleSignature RefinedSig;  // the intention is to use this field only after a successful PreResolve
    private ModuleSignature refinedSigOpened;

    internal override void PreResolve(ModuleDefinition m) {

      if (m.Implements?.Target.Decl == null) {
        // do this also for non-refining modules
        CheckSuperfluousRefiningMarks(m.TopLevelDecls, []);
        AddDefaultBaseTypeToUnresolvedNewtypes(m.TopLevelDecls);
      } else {
        // There is a refinement parent and it resolved OK
        var refinementTarget = m.Implements.Target;
        if (m.Implements.Kind == ImplementationKind.Refinement && refinementTarget.Def.ModuleKind == ModuleKindEnum.Replaceable) {
          Reporter.Error(MessageSource.RefinementTransformer, "refineReplaceable", refinementTarget.Origin,
            "replaceable module cannot be refined");

          return;
        }
        RefinedSig = refinementTarget.Sig;
        Contract.Assert(RefinedSig.ModuleDef != null);
        Contract.Assert(refinementTarget.Def == RefinedSig.ModuleDef);

        // check that the openness in the imports between refinement and its base matches
        Dictionary<string, TopLevelDecl> refinedModuleTopLevelDecls = new();
        foreach (var baseDecl in refinementTarget.Def.TopLevelDecls) {
          refinedModuleTopLevelDecls.Add(baseDecl.Name, baseDecl);
        }
        var declarations = m.TopLevelDecls;
        foreach (var mdecl in declarations.OfType<ModuleDecl>()) {
          if (refinedModuleTopLevelDecls.TryGetValue(mdecl.Name, out var baseDecl)) {
            if (baseDecl is ModuleDecl baseModuleDecl) {
              if (mdecl.Opened && !baseModuleDecl.Opened) {
                Error(ErrorId.ref_refinement_import_must_match_opened_base, m.Origin,
                  "{0} in {1} cannot be imported with \"opened\" because it does not match the corresponding import in the refinement base {2}.",
                  mdecl.Name, m.Name, m.Implements.Target.ToString());
              } else if (!mdecl.Opened && baseModuleDecl.Opened) {
                Error(ErrorId.ref_refinement_import_must_match_non_opened_base, m.Origin,
                  "{0} in {1} must be imported with \"opened\"  to match the corresponding import in its refinement base {2}.",
                  mdecl.Name, m.Name, m.Implements.Target.ToString());
              }
            }
          }
        }

        PreResolveWorker(m);
      }
    }

    void PreResolveWorker(ModuleDefinition module) {
      Contract.Requires(module != null);

      if (moduleUnderConstruction != null) {
        postTasks.Clear();
      }
      moduleUnderConstruction = module;
      refinementCloner = new RefinementCloner(moduleUnderConstruction);
      var refinementTarget = module.Implements.Target;
      var prev = refinementTarget.Def;

      //copy the signature, including its opened imports
      refinedSigOpened = ModuleResolver.MergeSignature(new ModuleSignature(), RefinedSig);
      ModuleResolver.ResolveOpenedImports(refinedSigOpened, prev, Reporter, null);

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, IPointer<TopLevelDecl>>();
      var pointers = module.TopLevelDeclPointers;
      foreach (var pointer in pointers) {
        var key = pointer.Get().Name;
        declaredNames.TryAdd(key, pointer);
      }

      // Merge the declarations of prev into the declarations of m
      List<string> processedDecl = [];
      foreach (var originalDeclaration in prev.TopLevelDecls) {
        processedDecl.Add(originalDeclaration.Name);
        if (!declaredNames.TryGetValue(originalDeclaration.Name, out var newPointer)) {
          var clone = refinementCloner.CloneDeclaration(originalDeclaration, module);
          module.SourceDecls.Add(clone);
        } else {
          var newDeclaration = newPointer.Get();
          if (originalDeclaration.Name == "_default" || newDeclaration.IsRefining || originalDeclaration is AbstractTypeDecl) {
            MergeTopLevelDecls(module, newPointer, originalDeclaration);
          } else if (newDeclaration is TypeSynonymDecl) {
            var msg = $"a type synonym ({newDeclaration.Name}) is not allowed to replace a {originalDeclaration.WhatKind} from the refined module ({module.Implements.Target}), even if it denotes the same type";
            Error(ErrorId.ref_refinement_type_must_match_base, newDeclaration.Origin, msg);
          } else if (!(originalDeclaration is AbstractModuleDecl)) {
            Error(ErrorId.ref_refining_notation_needed, newDeclaration.Origin, $"to redeclare and refine declaration '{originalDeclaration.Name}' from module '{module.Implements.Target}', you must use the refining (`...`) notation");
          }
        }
      }
      CheckSuperfluousRefiningMarks(module.TopLevelDecls, processedDecl);
      AddDefaultBaseTypeToUnresolvedNewtypes(module.TopLevelDecls);

      // Merge the imports of prev
      var prevTopLevelDecls = RefinedSig.TopLevels.Values;
      foreach (var d in prevTopLevelDecls) {
        if (!processedDecl.Contains(d.Name) && declaredNames.TryGetValue(d.Name, out var pointer)) {
          // if it is redefined, we need to merge them.
          MergeTopLevelDecls(module, pointer, d);
        }
      }
      refinementTarget.Sig = RefinedSig;

      Contract.Assert(moduleUnderConstruction == module);  // this should be as it was set earlier in this method
    }

    private void CheckSuperfluousRefiningMarks(IEnumerable<TopLevelDecl> topLevelDecls, List<string> excludeList) {
      Contract.Requires(topLevelDecls != null);
      Contract.Requires(excludeList != null);
      foreach (var d in topLevelDecls) {
        if (d.IsRefining && !excludeList.Contains(d.Name)) {
          Error(ErrorId.ref_refining_notation_does_not_refine, d.Origin, $"declaration '{d.Name}' indicates refining (notation `...`), but does not refine anything");
        }
      }
    }

    /// <summary>
    /// Give unresolved newtypes a reasonable default type (<c>int</c>), to avoid having to support `null` in the
    /// rest of the resolution pipeline.
    /// </summary>
    private void AddDefaultBaseTypeToUnresolvedNewtypes(IEnumerable<TopLevelDecl> topLevelDecls) {
      foreach (var d in topLevelDecls) {
        if (d is NewtypeDecl { IsRefining: true, BaseType: null } decl) {
          Reporter.Info(MessageSource.RefinementTransformer, decl.Origin, $"defaulting to 'int' for unspecified base type of '{decl.Name}'");
          decl.BaseType = new IntType(); // Set `BaseType` to some reasonable default to allow resolution to proceed
        }
      }
    }

    private void MergeModuleExports(ModuleExportDecl nw, ModuleExportDecl d) {
      if (nw.IsDefault != d.IsDefault) {
        Error(ErrorId.ref_default_export_unchangeable, nw, "can't change if a module export is default ({0})", nw.Name);
      }

      nw.Exports.AddRange(d.Exports);
      nw.Extends.AddRange(d.Extends);
    }

    private void MergeTopLevelDecls(ModuleDefinition m, IPointer<TopLevelDecl> nwPointer, TopLevelDecl d) {
      var nw = nwPointer.Get();
      var commonMsg = "a {0} declaration ({1}) in a refinement module can only refine a {0} declaration or replace an abstract type declaration";
      // Prefix decls.

      if (d is ModuleDecl) {
        if (!(nw is ModuleDecl)) {
          Error(ErrorId.ref_module_must_refine_module, nw, "a module ({0}) must refine another module", nw.Name);
        } else if (d is ModuleExportDecl) {
          if (!(nw is ModuleExportDecl)) {
            Error(ErrorId.ref_export_must_refine_export, nw, "a module export ({0}) must refine another export", nw.Name);
          } else {
            MergeModuleExports((ModuleExportDecl)nw, (ModuleExportDecl)d);
          }
        } else if (!(d is AbstractModuleDecl)) {
          Error(ErrorId.ref_base_module_must_be_facade, nw, "a module ({0}) can only refine a module facade", nw.Name);
        } else {
          // check that the new module refines the previous declaration
          if (!CheckIsRefinement((ModuleDecl)nw, (AbstractModuleDecl)d)) {
            Error(ErrorId.ref_module_must_refine_module_2, nw.Origin, "a module ({0}) can only be replaced by a refinement of the original module", d.Name);
          }
        }
      } else if (d is AbstractTypeDecl) {
        if (nw is ModuleDecl) {
          Error(ErrorId.ref_module_must_refine_module_2, nw, "a module ({0}) must refine another module", nw.Name);
        } else {
          var od = (AbstractTypeDecl)d;
          postTasks.Enqueue(() => {
            // check that od's type characteristics are respected by nw's
            var newType = UserDefinedType.FromTopLevelDecl(nw.Origin,
              nw is ClassLikeDecl { NonNullTypeDecl: { } nonNullTypeDecl } ? nonNullTypeDecl : nw);
            if (!CheckTypeCharacteristicsVisitor.CheckCharacteristics(od.Characteristics, newType, false, out var whatIsNeeded, out var hint, out var errorId)) {
              var typeCharacteristicsSyntax = od.Characteristics.ToString();
              Error(errorId, nw.Origin,
                $"to be a refinement of {od.WhatKind} '{od.EnclosingModuleDefinition.Name}.{od.Name}' declared with {typeCharacteristicsSyntax}, " +
                $"{nw.WhatKind} '{m.Name}.{nw.Name}' must {whatIsNeeded}{hint}");
            }
          });

          if (nw is TopLevelDeclWithMembers) {
            nwPointer.Set(MergeClass((TopLevelDeclWithMembers)nw, od));
          } else if (od.Members.Count != 0) {
            Error(ErrorId.ref_mismatched_type_with_members, nw,
              "a {0} ({1}) cannot declare members, so it cannot refine an abstract type with members",
              nw.WhatKind, nw.Name);
          } else {
            CheckAgreement_TypeParameters(nw.Origin, d.TypeArgs, nw.TypeArgs, nw.Name, "type");
          }
        }
      } else if (nw is AbstractTypeDecl) {
        Error(ErrorId.ref_mismatched_abstractness, nw,
          "an abstract type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
      } else if ((d is IndDatatypeDecl && nw is IndDatatypeDecl) || (d is CoDatatypeDecl && nw is CoDatatypeDecl)) {
        var (dd, nwd) = ((DatatypeDecl)d, (DatatypeDecl)nw);
        Contract.Assert(!nwd.Ctors.Any());
        nwd.Ctors.AddRange(dd.Ctors.Select(refinementCloner.CloneCtor));
        nwPointer.Set(MergeClass((DatatypeDecl)nw, (DatatypeDecl)d));
      } else if (nw is DatatypeDecl) {
        Error(ErrorId.ref_declaration_must_refine, nw, commonMsg, nw.WhatKind, nw.Name);
      } else if (d is NewtypeDecl && nw is NewtypeDecl) {
        var (dn, nwn) = ((NewtypeDecl)d, (NewtypeDecl)nw);
        Contract.Assert(nwn.BaseType == null && nwn.Var == null &&
                        nwn.Constraint == null && nwn.Witness == null);
        nwn.Var = dn.Var == null ? null : refinementCloner.CloneBoundVar(dn.Var, false);
        nwn.BaseType = nwn.Var?.Type ?? refinementCloner.CloneType(dn.BaseType); // Preserve newtype invariant that Var.Type is BaseType
        nwn.Constraint = dn.Constraint == null ? null : refinementCloner.CloneExpr(dn.Constraint);
        nwn.WitnessKind = dn.WitnessKind;
        nwn.Witness = dn.Witness == null ? null : refinementCloner.CloneExpr(dn.Witness);
        nwPointer.Set(MergeClass((NewtypeDecl)nw, (NewtypeDecl)d));
      } else if (nw is NewtypeDecl) {
        // `.Basetype` will be set in AddDefaultBaseTypeToUnresolvedNewtypes
        Error(ErrorId.ref_declaration_must_refine, nw, commonMsg, nw.WhatKind, nw.Name);
      } else if (nw is IteratorDecl) {
        if (d is IteratorDecl) {
          nwPointer.Set(MergeIterator((IteratorDecl)nw, (IteratorDecl)d));
        } else {
          Error(ErrorId.ref_iterator_must_refine_iterator, nw, "an iterator declaration ({0}) in a refining module cannot replace a different kind of declaration in the refinement base", nw.Name);
        }
      } else if (nw is TraitDecl) {
        if (d is TraitDecl) {
          nwPointer.Set(MergeClass((TraitDecl)nw, (TraitDecl)d));
        } else {
          Error(ErrorId.ref_declaration_must_refine, nw, commonMsg, nw.WhatKind, nw.Name);
        }
      } else if (nw is ClassDecl) {
        if (d is ClassDecl) {
          nwPointer.Set(MergeClass((ClassDecl)nw, (ClassDecl)d));
        } else {
          Error(ErrorId.ref_declaration_must_refine, nw, commonMsg, nw.WhatKind, nw.Name);
        }
      } else if (nw is DefaultClassDecl) {
        if (d is DefaultClassDecl) {
          nwPointer.Set((DefaultClassDecl)MergeClass((DefaultClassDecl)nw, (DefaultClassDecl)d));
        } else {
          Error(ErrorId.ref_declaration_must_refine, nw, commonMsg, nw.WhatKind, nw.Name);
        }
      } else if (nw is TypeSynonymDecl && d is TypeSynonymDecl && ((TypeSynonymDecl)nw).Rhs != null && ((TypeSynonymDecl)d).Rhs != null) {
        Error(ErrorId.ref_base_type_cannot_be_refined, d,
          "a type ({0}) in a refining module may not replace an already defined type (even with the same value)",
          d.Name);
      } else {
        Contract.Assert(false);
      }
    }

    public bool CheckIsRefinement(ModuleDecl derived, AbstractModuleDecl original) {
      // Check explicit refinement
      // TODO syntactic analysis of export sets is not quite right
      var derivedPointer = derived.Signature.ModuleDef;
      while (derivedPointer != null) {
        if (derivedPointer == original.OriginalSignature.ModuleDef) {
          HashSet<string> exports;
          if (derived is AliasModuleDecl) {
            exports = [.. ((AliasModuleDecl)derived).Exports.ConvertAll(t => t.val)];
          } else if (derived is AbstractModuleDecl) {
            exports = [.. ((AbstractModuleDecl)derived).Exports.ConvertAll(t => t.val)];
          } else {
            Error(ErrorId.ref_base_module_must_be_abstract_or_alias, derived, "a module ({0}) can only be refined by an alias module or a module facade", original.Name);
            return false;
          }
          var oexports = new HashSet<string>(original.Exports.ConvertAll(t => t.val));
          return oexports.IsSubsetOf(exports);
        }
        derivedPointer = derivedPointer.Implements.Target.Def;
      }
      return false;
    }

    internal override void PostResolveIntermediate(ModuleDefinition m) {
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

    Function CloneFunction(Function newFunction, Function previousFunction, Expression moreBody, Expression replacementBody, bool checkPrevPostconditions, Attributes moreAttributes) {
      Contract.Requires(moreBody == null || previousFunction is Predicate);
      Contract.Requires(moreBody == null || replacementBody == null);

      var tps = previousFunction.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam);
      var formals = previousFunction.Ins.ConvertAll(p => refinementCloner.CloneFormal(p, false));
      var req = previousFunction.Req.ConvertAll(refinementCloner.CloneAttributedExpr);
      var reads = refinementCloner.CloneSpecFrameExpr(previousFunction.Reads);
      var decreases = refinementCloner.CloneSpecExpr(previousFunction.Decreases);
      var result = previousFunction.Result ?? newFunction.Result;
      if (result != null) {
        result = refinementCloner.CloneFormal(result, false);
      }

      var ens = refinementCloner.WithRefinementTokenWrapping(
        () => previousFunction.Ens.ConvertAll(refinementCloner.CloneAttributedExpr),
        !checkPrevPostconditions); // note, if a postcondition includes something that changes in the module, the translator will notice this and still re-check the postcondition

      if (newFunction.Ens != null) {
        ens.AddRange(newFunction.Ens);
      }

      Expression body;
      Predicate.BodyOriginKind bodyOrigin;
      if (replacementBody != null) {
        body = replacementBody;
        bodyOrigin = Predicate.BodyOriginKind.DelayedDefinition;
      } else if (moreBody != null) {
        if (previousFunction.Body == null) {
          body = moreBody;
          bodyOrigin = Predicate.BodyOriginKind.DelayedDefinition;
        } else {
          body = new BinaryExpr(previousFunction.Origin, BinaryExpr.Opcode.And, refinementCloner.CloneExpr(previousFunction.Body), moreBody);
          bodyOrigin = Predicate.BodyOriginKind.Extension;
        }
      } else {
        body = refinementCloner.CloneExpr(previousFunction.Body);
        bodyOrigin = Predicate.BodyOriginKind.OriginalOrInherited;
      }
      var byMethodBody = refinementCloner.CloneBlockStmt(previousFunction.ByMethodBody);

      var origin = newFunction.Origin;
      var nameNode = newFunction.NameNode;

      if (previousFunction is Predicate) {
        return new Predicate(origin, nameNode, previousFunction.HasStaticKeyword, newFunction.IsGhost, previousFunction.IsOpaque, tps, formals, result,
          req, reads, ens, decreases, body, bodyOrigin,
          previousFunction.ByMethodTok == null ? null : refinementCloner.Origin(previousFunction.ByMethodTok), byMethodBody,
          refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      } else if (previousFunction is LeastPredicate) {
        return new LeastPredicate(origin, nameNode, previousFunction.HasStaticKeyword, previousFunction.IsOpaque, ((LeastPredicate)previousFunction).TypeOfK, tps, formals, result,
          req, reads, ens, body, refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      } else if (previousFunction is GreatestPredicate) {
        return new GreatestPredicate(origin, nameNode, previousFunction.HasStaticKeyword, previousFunction.IsOpaque, ((GreatestPredicate)previousFunction).TypeOfK, tps, formals, result,
          req, reads, ens, body, refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      } else if (previousFunction is TwoStatePredicate) {
        return new TwoStatePredicate(origin, nameNode, previousFunction.HasStaticKeyword, previousFunction.IsOpaque, tps, formals, result,
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      } else if (previousFunction is TwoStateFunction) {
        return new TwoStateFunction(origin, nameNode, previousFunction.HasStaticKeyword, previousFunction.IsOpaque, tps, formals, result, refinementCloner.CloneType(previousFunction.ResultType),
          req, reads, ens, decreases, body, refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      } else {
        return new Function(origin, nameNode, previousFunction.HasStaticKeyword, newFunction.IsGhost, previousFunction.IsOpaque, tps, formals, result, refinementCloner.CloneType(previousFunction.ResultType),
          req, reads, ens, decreases, body,
          previousFunction.ByMethodTok == null ? null : refinementCloner.Origin(previousFunction.ByMethodTok), byMethodBody,
          refinementCloner.MergeAttributes(previousFunction.Attributes, moreAttributes), null);
      }
    }

    MethodOrConstructor CloneMethod(MethodOrConstructor previousMethod, List<AttributedExpression> moreEnsures, Specification<Expression> decreases, BlockLikeStmt newBody, bool checkPreviousPostconditions, Attributes moreAttributes) {
      Contract.Requires(previousMethod != null);
      Contract.Requires(!(previousMethod is Constructor) || newBody == null || newBody is DividedBlockStmt);
      Contract.Requires(decreases != null);

      var tps = previousMethod.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam);
      var ins = previousMethod.Ins.ConvertAll(p => refinementCloner.CloneFormal(p, false));
      var req = previousMethod.Req.ConvertAll(refinementCloner.CloneAttributedExpr);
      var reads = refinementCloner.CloneSpecFrameExpr(previousMethod.Reads);
      var mod = refinementCloner.CloneSpecFrameExpr(previousMethod.Mod);

      var ens = refinementCloner.WithRefinementTokenWrapping(
        () => previousMethod.Ens.ConvertAll(refinementCloner.CloneAttributedExpr), !checkPreviousPostconditions);

      if (moreEnsures != null) {
        ens.AddRange(moreEnsures);
      }

      var origin = currentMethod.Origin;
      var newName = currentMethod.NameNode;
      if (previousMethod is Constructor) {
        var dividedBody = (DividedBlockStmt)newBody ?? refinementCloner.CloneDividedBlockStmt((DividedBlockStmt)previousMethod.Body);
        return new Constructor(origin, newName, previousMethod.IsGhost, tps, ins,
          req, reads, mod, ens, decreases, dividedBody, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes), null);
      }
      BlockStmt body = (BlockStmt)newBody ?? refinementCloner.CloneBlockStmt((BlockStmt)previousMethod.Body);
      if (previousMethod is LeastLemma) {
        return new LeastLemma(origin, newName, previousMethod.HasStaticKeyword, ((LeastLemma)previousMethod).TypeOfK, tps, ins,
          previousMethod.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)),
          req, reads, mod, ens, decreases, body, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes), null);
      } else if (previousMethod is GreatestLemma) {
        return new GreatestLemma(origin, newName, previousMethod.HasStaticKeyword, ((GreatestLemma)previousMethod).TypeOfK, tps, ins,
          previousMethod.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)),
          req, reads, mod, ens, decreases, body, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes), null);
      } else if (previousMethod is Lemma) {
        return new Lemma(origin, newName, previousMethod.HasStaticKeyword, tps, ins,
          previousMethod.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)),
          req, reads, mod, ens, decreases, body, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes), null);
      } else if (previousMethod is TwoStateLemma) {
        var two = (TwoStateLemma)previousMethod;
        return new TwoStateLemma(origin, newName, previousMethod.HasStaticKeyword, tps, ins,
          previousMethod.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)),
          req, reads, mod, ens, decreases, body, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes), null);
      } else if (previousMethod is Method previousMethodMethod) {
        return new Method(origin, newName, refinementCloner.MergeAttributes(previousMethod.Attributes, moreAttributes),
          previousMethod.HasStaticKeyword, previousMethod.IsGhost, tps, ins, req, ens, reads, decreases,
          previousMethod.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)),
          mod, body, null, previousMethodMethod.IsByMethod);
      } else {
        throw new Exception($"Cannot clone method type: {previousMethod.GetType().Name}");
      }
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    IteratorDecl MergeIterator(IteratorDecl nw, IteratorDecl prev) {
      Contract.Requires(nw != null);
      Contract.Requires(prev != null);

      if (nw.Requires.Count != 0) {
        Error(ErrorId.ref_no_new_iterator_preconditions, nw.Requires[0].E.Origin, "a refining iterator is not allowed to add preconditions");
      }
      if (nw.YieldRequires.Count != 0) {
        Error(ErrorId.ref_no_new_iterator_yield_preconditions, nw.YieldRequires[0].E.Origin, "a refining iterator is not allowed to add yield preconditions");
      }
      if (nw.Reads.Expressions.Count != 0) {
        Error(ErrorId.ref_no_new_iterator_reads, nw.Reads.Expressions[0].E.Origin, "a refining iterator is not allowed to extend the reads clause");
      }
      if (nw.Modifies.Expressions.Count != 0) {
        Error(ErrorId.ref_no_new_iterator_modifies, nw.Modifies.Expressions[0].E.Origin, "a refining iterator is not allowed to extend the modifies clause");
      }
      if (nw.Decreases.Expressions.Count != 0) {
        Error(ErrorId.ref_no_new_iterator_decreases, nw.Decreases.Expressions[0].Origin, "a refining iterator is not allowed to extend the decreases clause");
      }

      if (nw.SignatureIsOmitted) {
        Contract.Assert(nw.Ins.Count == 0);
        Contract.Assert(nw.Outs.Count == 0);
        Reporter.Info(MessageSource.RefinementTransformer, nw.SignatureEllipsis, Printer.IteratorSignatureToString(Reporter.Options, prev));
      } else {
        CheckAgreement_TypeParameters(nw.Origin, prev.TypeArgs, nw.TypeArgs, nw.Name, "iterator");
        CheckAgreement_Parameters(nw.Origin, prev.Ins, nw.Ins, nw.Name, "iterator", "in-parameter");
        CheckAgreement_Parameters(nw.Origin, prev.Outs, nw.Outs, nw.Name, "iterator", "yield-parameter");
      }

      BlockStmt newBody;
      if (nw.Body == null) {
        newBody = prev.Body;
      } else if (prev.Body == null) {
        newBody = nw.Body;
      } else {
        newBody = MergeBlockStmt(nw.Body, prev.Body);
      }

      var ens = refinementCloner.WithRefinementTokenWrapping(() =>
        prev.Ensures.ConvertAll(refinementCloner.CloneAttributedExpr));
      ens.AddRange(nw.Ensures);
      var yens = refinementCloner.WithRefinementTokenWrapping(() =>
        prev.YieldEnsures.ConvertAll(refinementCloner.CloneAttributedExpr));
      yens.AddRange(nw.YieldEnsures);

      return new IteratorDecl(nw.Origin.MakeRefined(moduleUnderConstruction),
        nw.NameNode, moduleUnderConstruction,
        nw.SignatureIsOmitted ? prev.TypeArgs.ConvertAll(refinementCloner.CloneTypeParam) : nw.TypeArgs,
        nw.SignatureIsOmitted ? prev.Ins.ConvertAll(p => refinementCloner.CloneFormal(p, false)) : nw.Ins,
        nw.SignatureIsOmitted ? prev.Outs.ConvertAll(o => refinementCloner.CloneFormal(o, false)) : nw.Outs,
        refinementCloner.CloneSpecFrameExpr(prev.Reads),
        refinementCloner.CloneSpecFrameExpr(prev.Modifies),
        refinementCloner.CloneSpecExpr(prev.Decreases),
        prev.Requires.ConvertAll(refinementCloner.CloneAttributedExpr),
        ens,
        prev.YieldRequires.ConvertAll(refinementCloner.CloneAttributedExpr),
        yens,
        newBody,
        refinementCloner.MergeAttributes(prev.Attributes, nw.Attributes),
        null);
    }

    TopLevelDeclWithMembers MergeClass(TopLevelDeclWithMembers nw, TopLevelDeclWithMembers prev) {
      CheckAgreement_TypeParameters(nw.Origin, prev.TypeArgs, nw.TypeArgs, nw.Name, nw.WhatKind);

      prev.Traits.ForEach(item => nw.Traits.Add(refinementCloner.CloneType(item)));
      nw.Attributes = refinementCloner.MergeAttributes(prev.Attributes, nw.Attributes);

      // Create a simple name-to-member dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < nw.Members.Count; i++) {
        var member = nw.Members[i];
        declaredNames.TryAdd(member.Name, i);
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var member in prev.Members) {
        if (!declaredNames.TryGetValue(member.Name, out var index)) {
          var nwMember = refinementCloner.CloneMember(member, false);
          nwMember.RefinementBase = member;
          nw.Members.Add(nwMember);
        } else {
          var nwMember = nw.Members[index];
          if (nwMember is ConstantField) {
            var newConst = (ConstantField)nwMember;
            var origConst = member as ConstantField;
            if (origConst == null) {
              Error(ErrorId.ref_const_must_refine_const, nwMember, "a const declaration ({0}) in a refining class ({1}) must replace a const in the refinement base", nwMember.Name, nw.Name);
            } else if (!(newConst.Type is InferredTypeProxy) && !TypesAreSyntacticallyEqual(newConst.Type, origConst.Type)) {
              Error(ErrorId.ref_no_changed_const_type, nwMember, "the type of a const declaration ({0}) in a refining class ({1}) must be syntactically the same as for the const being refined", nwMember.Name, nw.Name);
            } else if (newConst.Rhs != null && origConst.Rhs != null) {
              Error(ErrorId.ref_no_refining_const_initializer, nwMember, "a const re-declaration ({0}) can give an initializing expression only if the const in the refinement base does not", nwMember.Name);
            } else if (newConst.HasStaticKeyword != origConst.HasStaticKeyword) {
              Error(ErrorId.ref_mismatched_module_static, nwMember, "a const in a refining module cannot be changed from static to non-static or vice versa: {0}", nwMember.Name);
            } else if (origConst.IsGhost && !newConst.IsGhost) {
              Error(ErrorId.ref_mismatched_const_ghost, nwMember, "a const re-declaration ({0}) is not allowed to remove 'ghost' from the const declaration", nwMember.Name);
            } else if (newConst.Rhs == null && origConst.IsGhost == newConst.IsGhost) {
              Error(ErrorId.ref_refinement_must_add_const_ghost, nwMember, "a const re-declaration ({0}) must be to add 'ghost' to the const declaration{1}", nwMember.Name, origConst.Rhs == null ? " or to provide an initializing expression" : "");
            }
            nwMember.RefinementBase = member;
            // we may need to clone the given const declaration if either its type or initializing expression was omitted
            if (origConst != null) {
              if ((!(origConst.Type is InferredTypeProxy) && newConst.Type is InferredTypeProxy) || (origConst.Rhs != null && newConst.Rhs == null)) {
                var typ = newConst.Type is InferredTypeProxy ? refinementCloner.CloneType(origConst.Type) : newConst.Type;
                var rhs = newConst.Rhs ?? origConst.Rhs;
                nw.Members[index] = new ConstantField(newConst.Origin, newConst.NameNode, rhs, newConst.HasStaticKeyword, newConst.IsGhost, newConst.IsOpaque, typ, newConst.Attributes);
              }
            }

          } else if (nwMember is Field) {
            if (!(member is Field) || member is ConstantField) {
              Error(ErrorId.ref_field_must_refine_field, nwMember, "a field declaration ({0}) in a refining class ({1}) must replace a field in the refinement base", nwMember.Name, nw.Name);
            } else if (!TypesAreSyntacticallyEqual(((Field)nwMember).Type, ((Field)member).Type)) {
              Error(ErrorId.ref_mismatched_field_name, nwMember, "a field declaration ({0}) in a refining class ({1}) must repeat the syntactically same type as the field has in the refinement base", nwMember.Name, nw.Name);
            } else if (member.IsGhost || !nwMember.IsGhost) {
              Error(ErrorId.ref_refinement_field_must_add_ghost, nwMember, "a field re-declaration ({0}) must be to add 'ghost' to the field declaration", nwMember.Name);
            }
            nwMember.RefinementBase = member;

          } else if (nwMember is Function) {
            var f = (Function)nwMember;
            bool isPredicate = f is Predicate;
            bool isLeastPredicate = f is LeastPredicate;
            bool isGreatestPredicate = f is GreatestPredicate;
            if (!(member is Function) ||
              isPredicate != (member is Predicate) ||
              (f is LeastPredicate) != (member is LeastPredicate) ||
              (f is GreatestPredicate) != (member is GreatestPredicate) ||
              (f is TwoStatePredicate) != (member is TwoStatePredicate) ||
              (f is TwoStateFunction) != (member is TwoStateFunction)) {
              Error(ErrorId.ref_mismatched_refinement_kind, nwMember, "a {0} declaration ({1}) can only refine a {0}", f.WhatKind, nwMember.Name);
            } else {
              var prevFunction = (Function)member;
              if (f.Req.Count != 0) {
                Error(ErrorId.ref_refinement_no_new_preconditions, f.Req[0].E.Origin, "a refining {0} is not allowed to add preconditions", f.WhatKind);
              }
              if (f.Reads.Expressions.Count != 0) {
                Error(ErrorId.ref_refinement_no_new_reads, f.Reads.Expressions[0].E.Origin, "a refining {0} is not allowed to extend the reads clause", f.WhatKind);
              }
              if (f.Decreases.Expressions.Count != 0) {
                Error(ErrorId.ref_no_new_decreases, f.Decreases.Expressions[0].Origin, "decreases clause on refining {0} not supported", f.WhatKind);
              }

              if (prevFunction.HasStaticKeyword != f.HasStaticKeyword) {
                Error(ErrorId.ref_mismatched_function_static, f, "a function in a refining module cannot be changed from static to non-static or vice versa: {0}", f.Name);
              }
              if (!prevFunction.IsGhost && f.IsGhost) {
                Error(ErrorId.ref_mismatched_function_compile, f, "a compiled function cannot be changed into a ghost function in a refining module: {0}", f.Name);
              } else if (prevFunction.IsGhost && !f.IsGhost && prevFunction.Body != null) {
                Error(ErrorId.ref_no_refinement_function_with_body, f, "a ghost function can be changed into a compiled function in a refining module only if the function has not yet been given a body: {0}", f.Name);
              }
              if (f.SignatureIsOmitted) {
                Contract.Assert(f.TypeArgs.Count == 0);
                Contract.Assert(f.Ins.Count == 0);
                Reporter.Info(MessageSource.RefinementTransformer, f.SignatureEllipsis, Printer.FunctionSignatureToString(Reporter.Options, prevFunction));
              } else {
                CheckAgreement_TypeParameters(f.Origin, prevFunction.TypeArgs, f.TypeArgs, f.Name, "function");
                CheckAgreement_Parameters(f.Origin, prevFunction.Ins, f.Ins, f.Name, "function", "parameter");
                if (prevFunction.Result != null && f.Result != null && prevFunction.Result.Name != f.Result.Name) {
                  Error(ErrorId.ref_mismatched_function_return_name, f, "the name of function return value '{0}'({1}) differs from the name of corresponding function return value in the module it refines ({2})", f.Name, f.Result.Name, prevFunction.Result.Name);
                }
                if (!TypesAreSyntacticallyEqual(prevFunction.ResultType, f.ResultType)) {
                  Error(ErrorId.ref_mismatched_function_return_type, f, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", f.Name, f.ResultType, prevFunction.ResultType);
                }
              }

              Expression moreBody = null;
              Expression replacementBody = null;
              if (prevFunction.Body == null) {
                replacementBody = f.Body;
              } else if (f.Body != null) {
                Error(ErrorId.ref_mismatched_refinement_body, nwMember, $"a refining {f.WhatKind} is not allowed to extend/change the body");
              }
              var newF = CloneFunction(f, prevFunction, moreBody, replacementBody, prevFunction.Body == null, f.Attributes);
              newF.RefinementBase = member;
              nw.Members[index] = newF;
            }

          } else {
            var m = (MethodOrConstructor)nwMember;
            if (!(member is MethodOrConstructor prevMethod)) {
              Error(ErrorId.ref_method_refines_method, nwMember, "a method declaration ({0}) can only refine a method", nwMember.Name);
            } else {
              if (m.Req.Count != 0) {
                Error(ErrorId.ref_no_new_method_precondition, m.Req[0].E.Origin, "a refining method is not allowed to add preconditions");
              }
              if (m.Reads.Expressions.Count != 0) {
                Error(ErrorId.ref_no_new_method_reads, m.Reads.Expressions[0].E.Origin, "a refining method is not allowed to extend the reads clause");
              }
              if (m.Mod.Expressions.Count != 0) {
                Error(ErrorId.ref_no_new_method_modifies, m.Mod.Expressions[0].E.Origin, "a refining method is not allowed to extend the modifies clause");
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
                  Error(ErrorId.ref_no_new_method_decreases, m.Decreases.Expressions[0].Origin, "decreases clause on refining method not supported, unless the refined method was specified with 'decreases *'");
                }
                decreases = m.Decreases;
              }
              if (prevMethod.HasStaticKeyword != m.HasStaticKeyword) {
                Error(ErrorId.ref_mismatched_method_static, m, "a method in a refining module cannot be changed from static to non-static or vice versa: {0}", m.Name);
              }
              if (prevMethod.IsGhost && !m.IsGhost) {
                Error(ErrorId.ref_mismatched_method_ghost, m, "a ghost method cannot be changed into a non-ghost method in a refining module: {0}", m.Name);
              } else if (!prevMethod.IsGhost && m.IsGhost) {
                Error(ErrorId.ref_mismatched_method_non_ghost, m, "a method cannot be changed into a ghost method in a refining module: {0}", m.Name);
              }
              if (m.SignatureIsOmitted) {
                Contract.Assert(m.TypeArgs.Count == 0);
                Contract.Assert(m.Ins.Count == 0);
                Contract.Assert(m.Outs.Count == 0);
                Reporter.Info(MessageSource.RefinementTransformer, m.SignatureEllipsis, Printer.MethodSignatureToString(Reporter.Options, prevMethod));
              } else {
                CheckAgreement_TypeParameters(m.Origin, prevMethod.TypeArgs, m.TypeArgs, m.Name, "method");
                CheckAgreement_Parameters(m.Origin, prevMethod.Ins, m.Ins, m.Name, "method", "in-parameter");
                CheckAgreement_Parameters(m.Origin, prevMethod.Outs, m.Outs, m.Name, "method", "out-parameter");
              }
              currentMethod = m;
              var replacementBody = m.Body;
              if (replacementBody != null) {
                if (prevMethod.Body == null) {
                  // cool
                } else {
                  replacementBody = MergeBlockLikeStmt(replacementBody, prevMethod.Body);
                }
              }
              var newM = CloneMethod(prevMethod, m.Ens, decreases, replacementBody, prevMethod.Body == null, m.Attributes);
              newM.RefinementBase = prevMethod;
              nw.Members[index] = newM;
            }
          }
        }
      }

      return nw;
    }
    void CheckAgreement_TypeParameters(IOrigin tok, List<TypeParameter> old, List<TypeParameter> nw, string name, string thing) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      if (old.Count != nw.Count) {
        Error(ErrorId.ref_mismatched_type_parameters_count, tok, "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than the corresponding {0} in the module it refines", thing, name, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            Error(ErrorId.ref_mismatched_type_parameter_name, n.Origin, "type parameters are not allowed to be renamed from the names given in the {0} in the module being refined (expected '{1}', found '{2}')", thing, o.Name, n.Name);
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
              Error(ErrorId.ref_mismatched_type_parameter_equality, n.Origin, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
            }
            if (o.Characteristics.HasCompiledValue != n.Characteristics.HasCompiledValue) {
              Error(ErrorId.ref_mismatched_type_parameter_auto_init, n.Origin, "type parameter '{0}' is not allowed to change the requirement of supporting auto-initialization", n.Name);
            } else if (o.Characteristics.IsNonempty != n.Characteristics.IsNonempty) {
              Error(ErrorId.ref_mismatched_type_parameter_nonempty, n.Origin, "type parameter '{0}' is not allowed to change the requirement of being nonempty", n.Name);
            }
            if (o.Characteristics.ContainsNoReferenceTypes != n.Characteristics.ContainsNoReferenceTypes) {
              Error(ErrorId.ref_mismatched_type_parameter_not_reference, n.Origin, "type parameter '{0}' is not allowed to change the no-reference-type requirement", n.Name);
            }
            if (o.Variance != n.Variance) {  // syntax is allowed to be different as long as the meaning is the same (i.e., compare Variance, not VarianceSyntax)
              var ov = o.Variance == TypeParameter.TPVariance.Co ? "+" : o.Variance == TypeParameter.TPVariance.Contra ? "-" : "=";
              var nv = n.Variance == TypeParameter.TPVariance.Co ? "+" : n.Variance == TypeParameter.TPVariance.Contra ? "-" : "=";
              Error(ErrorId.ref_mismatched_type_parameter_variance, n.Origin, "type parameter '{0}' is not allowed to change variance (here, from '{1}' to '{2}')", n.Name, ov, nv);
            }

            CheckAgreement_TypeBounds(n.Origin, o, n, name, thing);
          }
        }
      }
    }

    void CheckAgreement_TypeBounds(IOrigin tok, TypeParameter old, TypeParameter nw, string name, string thing) {
      if (old.TypeBounds.Count != nw.TypeBounds.Count) {
        Error(ErrorId.ref_mismatched_type_bounds_count, tok,
          $"type parameter '{nw.Name}' of {thing} '{name}' is declared with a different number of type bounds than in the corresponding {thing}" +
          $" in the module it refines (expected {old.TypeBounds.Count}, found {nw.TypeBounds.Count})");
        return;
      }
      for (var i = 0; i < old.TypeBounds.Count; i++) {
        var oldBound = old.TypeBounds[i];
        var newBound = nw.TypeBounds[i];
        if (!TypesAreSyntacticallyEqual(oldBound, newBound)) {
          Error(ErrorId.ref_mismatched_type_parameter_bound, tok,
            $"type bound for type parameter '{nw.Name}' of {thing} '{name}' is different from the corresponding type bound of the " +
            $"corresponding type parameter of the corresponding {thing} in the module it refines (expected '{oldBound}', found '{newBound}')");
        }
      }
    }

    void CheckAgreement_Parameters(IOrigin tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(parameterKind != null);
      if (old.Count != nw.Count) {
        Error(ErrorId.ref_mismatched_kind_count, tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            Error(ErrorId.ref_mismatched_kind_name, n.Origin, "there is a difference in name of {0} {1} ('{2}' versus '{3}') of {4} {5} compared to corresponding {4} in the module it refines", parameterKind, i, n.Name, o.Name, thing, name);
          } else if (!o.IsGhost && n.IsGhost) {
            Error(ErrorId.ref_mismatched_kind_ghost, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            Error(ErrorId.ref_mismatched_kind_non_ghost, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!o.IsOld && n.IsOld) {
            Error(ErrorId.ref_mismatched_kind_non_new, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from new to non-new", parameterKind, n.Name, thing, name);
          } else if (o.IsOld && !n.IsOld) {
            Error(ErrorId.ref_mismatched_kind_new, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-new to new", parameterKind, n.Name, thing, name);
          } else if (!o.IsOlder && n.IsOlder) {
            Error(ErrorId.ref_mismatched_kind_older, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-older to older", parameterKind, n.Name, thing, name);
          } else if (o.IsOlder && !n.IsOlder) {
            Error(ErrorId.ref_mismatched_kind_non_older, n.Origin, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from older to non-older", parameterKind, n.Name, thing, name);
          } else if (!TypesAreSyntacticallyEqual(o.Type, n.Type)) {
            Error(ErrorId.ref_mismatched_parameter_type, n.Origin, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
          } else if (n.DefaultValue != null) {
            Error(ErrorId.ref_refined_formal_may_not_have_default, n.Origin, "a refining formal parameter ('{0}') in a refinement module is not allowed to give a default-value expression", n.Name);
          }
        }
      }
    }

    bool TypesAreSyntacticallyEqual(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      return t.ToString() == u.ToString();
    }

    /// <summary>
    /// This method merges the statement "oldStmt" into the template "skeleton".
    /// </summary>
    BlockLikeStmt MergeBlockLikeStmt(BlockLikeStmt skeleton, BlockLikeStmt oldStmt) {
      if (skeleton is BlockStmt blockStmt) {
        return MergeBlockStmt(blockStmt, (BlockStmt)oldStmt);
      } else {
        return MergeDividedBlockStmt((DividedBlockStmt)skeleton, (DividedBlockStmt)oldStmt);
      }
    }

    /// <summary>
    /// This method merges the statement "oldStmt" into the template "skeleton".
    /// </summary>
    DividedBlockStmt MergeDividedBlockStmt(DividedBlockStmt skeleton, DividedBlockStmt oldStmt) {
      Contract.Requires(skeleton != null);
      Contract.Requires(oldStmt != null);

      var sbsSkeleton = skeleton;
      var sbsOldStmt = oldStmt;
      var bodyInit = MergeStmtList(sbsSkeleton.BodyInit, sbsOldStmt.BodyInit, out var hoverText);
      if (hoverText.Length != 0) {
        Reporter.Info(MessageSource.RefinementTransformer, sbsSkeleton.SeparatorTok ?? sbsSkeleton.Origin, hoverText);
      }

      var bodyProper = MergeStmtList(sbsSkeleton.BodyProper, sbsOldStmt.BodyProper, out hoverText);
      if (hoverText.Length != 0) {
        Reporter.Info(MessageSource.RefinementTransformer, sbsSkeleton.Origin, hoverText);
      }

      return new DividedBlockStmt(sbsSkeleton.Origin, bodyInit, sbsSkeleton.SeparatorTok, bodyProper, sbsSkeleton.Labels);
    }

    /// <summary>
    /// This method merges the statement "oldStmt" into the template "skeleton".
    /// </summary>
    BlockStmt MergeBlockStmt(BlockStmt skeleton, BlockStmt oldStmt) {
      Contract.Requires(skeleton != null);
      Contract.Requires(oldStmt != null);

      var body = MergeStmtList(skeleton.Body, oldStmt.Body, out var hoverText);
      if (hoverText.Length != 0) {
        Reporter.Info(MessageSource.RefinementTransformer, skeleton.Origin, hoverText);
      }
      return new BlockStmt(skeleton.Origin, body);
    }

    List<Statement> MergeStmtList(IReadOnlyList<Statement> skeleton, IReadOnlyList<Statement> oldStmt, out string hoverText) {
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
            Error(ErrorId.ref_mismatched_skeleton, cur.Origin, "skeleton statement does not match old statement");
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
            var skeletonStatementType = c.S;
            if (skeletonStatementType == null) {
              var nxt = i + 1 == skeleton.Count ? null : skeleton[i + 1];
              if (nxt != null && nxt is SkeletonStatement && ((SkeletonStatement)nxt).S == null) {
                // "...; ...;" is the same as just "...;", so skip this one
              } else {
                // skip up until the next thing that matches "nxt"
                var hoverTextA = "";
                var sepA = "";
                while (nxt == null || !PotentialMatch(nxt, oldS)) {
                  // loop invariant:  oldS == oldStmt.Body[j]
                  var s = refinementCloner.CloneStmt(oldS, false);
                  body.Add(s);
                  hoverTextA += sepA + Printer.StatementToString(Reporter.Options, s);
                  sepA = "\n";
                  j++;
                  if (j == oldStmt.Count) { break; }
                  oldS = oldStmt[j];
                }
                if (hoverTextA.Length != 0) {
                  Reporter.Info(MessageSource.RefinementTransformer, c.Origin, hoverTextA);
                }
              }
              i++;

            } else if (skeletonStatementType is AssertStmt skeletonAssert) {
              Contract.Assert(c.ConditionOmitted);
              var oldPredicateStmt = oldS as PredicateStmt;
              if (oldPredicateStmt == null) {
                Error(ErrorId.ref_mismatched_assert, cur.Origin, "assert template does not match inherited statement");
                i++;
              } else {
                // Clone the expression, but among the new assert's attributes, indicate
                // that this assertion is supposed to be translated into a check.  That is,
                // it is not allowed to be just assumed in the translation, despite the fact
                // that the condition is inherited.
                var e = refinementCloner.CloneExpr(oldPredicateStmt.Expr);
                var attrs = refinementCloner.MergeAttributes(oldPredicateStmt.Attributes, skeletonAssert.Attributes);
                body.Add(new AssertStmt(new NestedOrigin(skeletonAssert.Origin, oldPredicateStmt.Expr.Origin, "refined proposition"), e, skeletonAssert.Label, attrs));
                Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, "assume->assert: " + Printer.ExprToString(Reporter.Options, e));
                i++; j++;
              }

            } else if (skeletonStatementType is ExpectStmt) {
              var skel = (ExpectStmt)skeletonStatementType;
              Contract.Assert(c.ConditionOmitted);
              var oldExpect = oldS as ExpectStmt;
              if (oldExpect == null) {
                Error(ErrorId.ref_mismatched_expect, cur.Origin, "expect template does not match inherited statement");
                i++;
              } else {
                var e = refinementCloner.CloneExpr(oldExpect.Expr);
                var message = refinementCloner.CloneExpr(oldExpect.Message);
                var attrs = refinementCloner.MergeAttributes(oldExpect.Attributes, skel.Attributes);
                body.Add(new ExpectStmt(skel.Origin, e, message, attrs));
                Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.ExprToString(Reporter.Options, e));
                i++; j++;
              }

            } else if (skeletonStatementType is AssumeStmt) {
              var skel = (AssumeStmt)skeletonStatementType;
              Contract.Assert(c.ConditionOmitted);
              var oldAssume = oldS as AssumeStmt;
              if (oldAssume == null) {
                Error(ErrorId.ref_mismatched_assume, cur.Origin, "assume template does not match inherited statement");
                i++;
              } else {
                var e = refinementCloner.CloneExpr(oldAssume.Expr);
                var attrs = refinementCloner.MergeAttributes(oldAssume.Attributes, skel.Attributes);
                body.Add(new AssumeStmt(skel.Origin, e, attrs));
                Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.ExprToString(Reporter.Options, e));
                i++; j++;
              }

            } else if (skeletonStatementType is IfStmt) {
              var skel = (IfStmt)skeletonStatementType;
              Contract.Assert(c.ConditionOmitted);
              var oldIf = oldS as IfStmt;
              if (oldIf == null) {
                Error(ErrorId.ref_mismatched_if_statement, cur.Origin, "if-statement template does not match inherited statement");
                i++;
              } else {
                var resultingThen = MergeBlockStmt(skel.Thn, oldIf.Thn);
                var resultingElse = MergeElse(skel.Els, oldIf.Els);
                var e = refinementCloner.CloneExpr(oldIf.Guard);
                var r = new IfStmt(skel.Origin, oldIf.IsBindingGuard, e, (BlockStmt)resultingThen, resultingElse);
                body.Add(r);
                Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.GuardToString(Reporter.Options, oldIf.IsBindingGuard, e));
                i++; j++;
              }

            } else if (skeletonStatementType is WhileStmt) {
              var skel = (WhileStmt)skeletonStatementType;
              var oldWhile = oldS as WhileStmt;
              if (oldWhile == null) {
                Error(ErrorId.ref_mismatched_while_statement, cur.Origin, "while-statement template does not match inherited statement");
                i++;
              } else {
                Expression guard;
                if (c.ConditionOmitted) {
                  guard = refinementCloner.CloneExpr(oldWhile.Guard);
                  Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.GuardToString(Reporter.Options, false, oldWhile.Guard));
                } else {
                  if (oldWhile.Guard != null) {
                    Error(ErrorId.ref_mismatched_while_statement_guard, skel.Guard.Origin, "a skeleton while statement with a guard can only replace a while statement with a non-deterministic guard");
                  }
                  guard = skel.Guard;
                }
                // Note, if the loop body is omitted in the skeleton, the parser will have set the loop body to an empty block,
                // which has the same merging behavior.
                var r = MergeWhileStmt(skel, oldWhile, guard);
                body.Add(r);
                i++; j++;
              }

            } else if (skeletonStatementType is ModifyStmt) {
              var skel = (ModifyStmt)skeletonStatementType;
              Contract.Assert(c.ConditionOmitted);
              var oldModifyStmt = oldS as ModifyStmt;
              if (oldModifyStmt == null) {
                Error(ErrorId.ref_mismatched_modify_statement, cur.Origin, "modify template does not match inherited statement");
                i++;
              } else {
                var mod = refinementCloner.CloneSpecFrameExpr(oldModifyStmt.Mod);
                BlockStmt mbody;
                if (oldModifyStmt.Body == null && skel.Body == null) {
                  mbody = null;
                } else if (oldModifyStmt.Body == null) {
                  // Note, it is important to call MergeBlockStmt here (rather than just setting "mbody" to "skel.Body"), even
                  // though we're passing in an empty block as its second argument. The reason for this is that MergeBlockStmt
                  // also sets ".ReverifyPost" to "true" for any "return" statements.
                  mbody = MergeBlockStmt(skel.Body, new BlockStmt(oldModifyStmt.Origin, []));
                } else if (skel.Body == null) {
                  Error(ErrorId.ref_mismatched_statement_body, cur.Origin, "modify template must have a body if the inherited modify statement does");
                  mbody = null;
                } else {
                  mbody = MergeBlockStmt(skel.Body, oldModifyStmt.Body);
                }
                body.Add(new ModifyStmt(skel.Origin, mod.Expressions, mod.Attributes, mbody));
                Reporter.Info(MessageSource.RefinementTransformer, c.ConditionEllipsis, Printer.FrameExprListToString(Reporter.Options, mod.Expressions));
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
                var update = cNew.Assign as AssignStatement;
                if (update != null && update.Rhss.TrueForAll(rhs => !rhs.CanAffectPreviouslyKnownExpressions)) {
                  // Note, we allow switching between ghost and non-ghost, since that seems unproblematic.
                  if (cOld.Assign == null) {
                    doMerge = true;
                  } else if (cOld.Assign is AssignSuchThatStmt) {
                    doMerge = true;
                    addedAssert = refinementCloner.CloneExpr(((AssignSuchThatStmt)cOld.Assign).Expr);
                  } else {
                    var updateOld = (AssignStatement)cOld.Assign;  // if cast fails, there are more ConcreteUpdateStatement subclasses than expected
                    doMerge = true;
                    foreach (var rhs in updateOld.Rhss) {
                      if (!(rhs is HavocRhs)) {
                        doMerge = false;
                      }
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
                var tok = new BoogieGenerator.ForceCheckOrigin(addedAssert.Origin);
                body.Add(new AssertStmt(tok, addedAssert, null, null));
              }
            } else {
              MergeAddStatement(cur, body);
              i++;
            }

          } else if (cur is SingleAssignStmt) {
            var cNew = (SingleAssignStmt)cur;
            var cOld = oldS as SingleAssignStmt;
            if (cOld == null && oldS is AssignStatement) {
              var us = (AssignStatement)oldS;
              if (us.ResolvedStatements.Count == 1) {
                cOld = us.ResolvedStatements[0] as SingleAssignStmt;
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

          } else if (cur is AssignStatement) {
            var nw = (AssignStatement)cur;
            List<Statement> stmtGenerated = [];
            bool doMerge = false;
            if (oldS is AssignStatement) {
              var s = (AssignStatement)oldS;
              if (LeftHandSidesAgree(s.Lhss, nw.Lhss)) {
                doMerge = true;
                stmtGenerated.Add(nw);
                foreach (var rhs in s.Rhss) {
                  if (!(rhs is HavocRhs)) {
                    doMerge = false;
                  }
                }
              }
            } else if (oldS is AssignSuchThatStmt) {
              var s = (AssignSuchThatStmt)oldS;
              if (LeftHandSidesAgree(s.Lhss, nw.Lhss)) {
                doMerge = true;
                stmtGenerated.Add(nw);
                var addedAssert = refinementCloner.CloneExpr(s.Expr);
                var tok = new SourceOrigin(addedAssert.StartToken, addedAssert.EndToken);
                stmtGenerated.Add(new AssertStmt(tok, addedAssert, null, null));
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
              var r = new IfStmt(cNew.Origin, cNew.IsBindingGuard, cNew.Guard, MergeBlockStmt(cNew.Thn, cOld.Thn), MergeElse(cNew.Els, cOld.Els));
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
          } else if (cur is LabeledStatement) {
            MergeAddStatement(cur, body);
            i++;
            j++;
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
        body.Add(refinementCloner.CloneStmt(b, false));
        hoverText += sep + Printer.StatementToString(Reporter.Options, b);
        sep = "\n";
      }
      return body;
    }

    private bool LeftHandSidesAgree(List<Expression> old, List<Expression> nw) {
      if (old.Count != nw.Count) {
        return false;
      }

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
      if (old.Count != nw.Count) {
        return false;
      }

      for (int i = 0; i < old.Count; i++) {
        if (old[i].Name != nw[i].Name) {
          return false;
        }
      }
      return true;
    }

    bool PotentialMatch(Statement nxt, Statement other) {
      Contract.Requires(nxt != null);
      Contract.Requires(!(nxt is SkeletonStatement) || ((SkeletonStatement)nxt).S != null);  // nxt is not "...;"
      Contract.Requires(other != null);

      if (nxt is LabeledStatement nextLabelled && other is LabeledStatement otherLabelled && nextLabelled.Labels.Any()) {
        foreach (var olbl in otherLabelled.Labels) {
          foreach (var l in nextLabelled.Labels) {
            if (olbl.Name == l.Name) {
              return true;
            }
          }
        }
        return false;  // labels of 'nxt' don't match any label of 'other'
      } else if (nxt is SkeletonStatement statement) {
        var S = statement.S;
        if (S is AssertStmt) {
          return other is PredicateStmt;
        } else if (S is ExpectStmt) {
          return other is ExpectStmt;
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
        if (b.Labels.Any()) {
          if (other is BlockStmt oth && oth.Labels.Any()) {
            return b.Labels.First().Name == oth.Labels.First().Name; // both have the same label
          }
        } else if (other is BlockStmt stmt && !stmt.Labels.Any()) {
          return true; // both are unlabeled
        }
      } else if (nxt is AssignStatement) {
        var up = (AssignStatement)nxt;
        if (other is AssignSuchThatStmt oth) {
          return LeftHandSidesAgree(oth.Lhss, up.Lhss);
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
          Error(ErrorId.ref_mismatched_loop_decreases, cNew.Decreases.Expressions[0].Origin, "a refining loop can provide a decreases clause only if the loop being refined was declared with 'decreases *'");
        }
        decr = cNew.Decreases;
      }

      var invs = cOld.Invariants.ConvertAll(refinementCloner.CloneAttributedExpr);
      invs.AddRange(cNew.Invariants);
      BlockStmt newBody;
      if (cOld.Body == null && cNew.Body == null) {
        newBody = null;
      } else if (cOld.Body == null) {
        newBody = MergeBlockStmt(cNew.Body, new BlockStmt(cOld.Origin, []));
      } else if (cNew.Body == null) {
        Error(ErrorId.ref_mismatched_while_body, cNew.Origin, "while template must have a body if the inherited while statement does");
        newBody = null;
      } else {
        newBody = MergeBlockStmt(cNew.Body, cOld.Body);
      }
      return new RefinedWhileStmt(cNew.Origin, guard, invs, decr, refinementCloner.CloneSpecFrameExpr(cOld.Mod), newBody);
    }

    Statement MergeElse(Statement skeleton, Statement oldStmt) {
      Contract.Requires(skeleton == null || skeleton is BlockStmt || skeleton is IfStmt || skeleton is SkeletonStatement);
      Contract.Requires(oldStmt == null || oldStmt is BlockStmt || oldStmt is IfStmt || oldStmt is SkeletonStatement);

      if (skeleton == null) {
        return refinementCloner.CloneStmt(oldStmt, false);
      } else if (skeleton is IfStmt || skeleton is SkeletonStatement) {
        // wrap a block statement around the if statement
        skeleton = new BlockStmt(skeleton.Origin, [skeleton]);
      }

      if (oldStmt == null) {
        // make it into an empty block statement
        oldStmt = new BlockStmt(skeleton.Origin, []);
      } else if (oldStmt is IfStmt || oldStmt is SkeletonStatement) {
        // wrap a block statement around the if statement
        oldStmt = new BlockStmt(skeleton.Origin, [oldStmt]);
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
      var prevErrorCount = Reporter.Count(ErrorLevel.Error);
      CheckIsOkayNewStatement(s, new Stack<string>(), 0);
      if (Reporter.Count(ErrorLevel.Error) == prevErrorCount) {
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

      if (s is LabeledStatement labelledStatement) {
        foreach (var n in labelledStatement.Labels) {
          labels.Push(n.Name);
        }
      }
      if (s is SkeletonStatement) {
        Error(ErrorId.ref_misplaced_skeleton, s, "skeleton statement may not be used here; it does not have a matching statement in what is being replaced");
      } else if (s is ReturnStmt) {
        // allow return statements, but make note of that this requires verifying the postcondition
        ((ReturnStmt)s).ReverifyPost = true;
      } else if (s is YieldStmt) {
        Error(ErrorId.ref_misplaced_yield, s, "yield statements are not allowed in skeletons");
      } else if (s is BreakOrContinueStmt) {
        var b = (BreakOrContinueStmt)s;
        if (b.TargetLabel != null ? !labels.Contains(b.TargetLabel.Value) : loopLevels < b.BreakAndContinueCount) {
          Error(ErrorId.ref_invalid_break_in_skeleton, s, $"{b.Kind} statement in skeleton is not allowed to break outside the skeleton fragment");
        }
      } else if (s is SingleAssignStmt) {
        // TODO: To be a refinement automatically (that is, without any further verification), only variables and fields defined
        // in this module are allowed.  This needs to be checked.  If the LHS refers to an l-value that was not declared within
        // this module, then either an error should be reported or the Translator needs to know to translate new proof obligations.
        var a = (SingleAssignStmt)s;
        Error(ErrorId.ref_misplaced_assignment, a.Origin, "cannot have assignment statement");
      } else if (s is ConcreteAssignStatement) {
        postTasks.Enqueue(() => {
          CheckIsOkayUpdateStmt((ConcreteAssignStatement)s, moduleUnderConstruction);
        });
      } else if (s is CallStmt) {
        Error(ErrorId.ref_misplaced_call, s.Origin, "cannot have call statement");
      } else {
        if (s is WhileStmt || s is AlternativeLoopStmt) {
          loopLevels++;
        }
        foreach (var ss in s.SubStatements) {
          CheckIsOkayNewStatement(ss, labels, loopLevels);
        }
      }

      if (s is LabeledStatement labelledStatement2) {
        foreach (var n in labelledStatement2.Labels) {
          labels.Pop();
        }
      }
    }

    // Checks that statement stmt, defined in the constructed module m, is a refinement of skip in the parent module
    void CheckIsOkayUpdateStmt(ConcreteAssignStatement stmt, ModuleDefinition m) {
      foreach (var lhs in stmt.Lhss) {
        var l = lhs.Resolved;
        if (l is IdentifierExpr) {
          var ident = (IdentifierExpr)l;
          Contract.Assert(ident.Var is LocalVariable || ident.Var is Formal); // LHS identifier expressions must be locals or out parameters (ie. formals)
          if ((ident.Var is LocalVariable && ((LocalVariable)ident.Var).Origin.IsInherited(m)) || ident.Var is Formal) {
            // for some reason, formals are not considered to be inherited.
            Error(ErrorId.ref_invalid_variable_assignment, l.Origin, "refinement method cannot assign to variable defined in parent module ('{0}')", ident.Var.Name);
          }
        } else if (l is MemberSelectExpr) {
          var member = ((MemberSelectExpr)l).Member;
          if (member.Origin.IsInherited(m)) {
            Error(ErrorId.ref_invalid_field_assignment, l.Origin, "refinement method cannot assign to a field defined in parent module ('{0}')", member.Name);
          }
        } else {
          // must be an array element
          Error(ErrorId.ref_invalid_new_assignments, l.Origin, "new assignments in a refinement method can only assign to state that the module defines (which never includes array elements)");
        }
      }
      if (stmt is AssignStatement) {
        var s = (AssignStatement)stmt;
        foreach (var rhs in s.Rhss) {
          if (rhs.CanAffectPreviouslyKnownExpressions) {
            Error(ErrorId.ref_invalid_assignment_rhs, rhs.Origin, "assignment RHS in refinement method is not allowed to affect previously defined state");
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
        if (e.Function.EnclosingClass.EnclosingModuleDefinition == m) {
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
    readonly ModuleDefinition moduleUnderConstruction;
    private bool wrapWithRefinementToken = true;

    public RefinementCloner(ModuleDefinition m) : base(false, false) {
      moduleUnderConstruction = m;
    }

    public override BlockLikeStmt CloneMethodBody(MethodOrConstructor m) {
      if (m.Body is DividedBlockStmt) {
        return CloneDividedBlockStmt((DividedBlockStmt)m.Body);
      } else {
        return CloneBlockStmt((BlockStmt)m.Body);
      }
    }

    [Pure]
    public T WithRefinementTokenWrapping<T>(Func<T> action, bool wrap = false) {
      var current = wrapWithRefinementToken;
      wrapWithRefinementToken = wrap;
      var result = action();
      wrapWithRefinementToken = current;
      return result;
    }

    public override IOrigin Origin(IOrigin tok) {
      if (tok == null) {
        return null;
      }

      if (wrapWithRefinementToken) {
        return new RefinementOrigin(tok, moduleUnderConstruction);
      }

      return tok;
    }
    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition newParent) {
      var dd = base.CloneDeclaration(d, newParent);
      if (dd is ModuleExportDecl ddex) {
        // In refinement cloning, a default export set from the parent should, in the
        // refining module, retain its name but not be default, unless the refining module has the same name
        ModuleExportDecl dex = d as ModuleExportDecl;
        if (dex.IsDefault && d.Name != newParent.Name) {
          ddex = new ModuleExportDecl(ddex.Options, dex.Origin, d.NameNode, d.Attributes, newParent, dex.Exports, dex.Extends,
            dex.ProvideAll, dex.RevealAll, false, true, Guid.NewGuid());
        }
        ddex.SetupDefaultSignature();
        dd = ddex;
      } else if (d is ModuleDecl) {
        ((ModuleDecl)dd).Signature = ((ModuleDecl)d).Signature;
        if (d is AbstractModuleDecl) {
          ((AbstractModuleDecl)dd).OriginalSignature = ((AbstractModuleDecl)d).OriginalSignature;
        }
      }
      return dd;
    }
    public virtual Attributes MergeAttributes(Attributes prevAttrs, Attributes moreAttrs) {
      if (moreAttrs == null) {
        return CloneAttributes(prevAttrs);
      } else if (moreAttrs is UserSuppliedAttributes) {
        var usa = (UserSuppliedAttributes)moreAttrs;
        return new UserSuppliedAttributes(Origin(usa.Origin), Origin(usa.OpenBrace), Origin(usa.CloseBrace), moreAttrs.Args.ConvertAll(CloneExpr), MergeAttributes(prevAttrs, moreAttrs.Prev));
      } else if (moreAttrs is UserSuppliedAtAttribute usaa) {
        var arg = CloneExpr(usaa.Arg);
        if (usaa.Arg.Type != null) { // The attribute has already been expanded
          arg.Type = usaa.Arg.Type;
          arg.PreType = usaa.Arg.PreType;
        }
        return new UserSuppliedAtAttribute(Origin(usaa.Origin), arg, MergeAttributes(prevAttrs, moreAttrs.Prev)) {
          Builtin = usaa.Builtin
        };
      } else {
        return new Attributes(moreAttrs.Name, moreAttrs.Args.ConvertAll(CloneExpr), MergeAttributes(prevAttrs, moreAttrs.Prev));
      }
    }
  }
}
