//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using DafnyCore.Verifier;

namespace Microsoft.Dafny {
  public class ProofDependencyManager {
    // proof dependency tracking state
    public Dictionary<string, ProofDependency> ProofDependenciesById { get; } = new();
    public readonly Dictionary<string, (Declaration Decl, HashSet<ProofDependency> Deps)> idsByMemberName = new();
    private UInt64 proofDependencyIdCount = 0;
    private string currentDeclarationString;
    private Declaration currentDeclaration;

    public string GetProofDependencyId(ProofDependency dep) {
      var idString = $"id{proofDependencyIdCount}";
      ProofDependenciesById[idString] = dep;
      proofDependencyIdCount++;
      var (_, currentSet) = idsByMemberName.GetOrCreate(currentDeclarationString, () => (currentDeclaration, new HashSet<ProofDependency>()));
      currentSet.Add(dep);
      return idString;
    }

    public void SetCurrentDefinition(string verificationScopeId, Declaration decl) {
      currentDeclarationString = verificationScopeId;
      currentDeclaration = decl;
    }

    public IEnumerable<ProofDependency> GetPotentialDependenciesForDefinition(string defName) {
      return idsByMemberName.TryGetValue(defName, out var result) ? result.Deps : Enumerable.Empty<ProofDependency>();
    }

    public IEnumerable<ProofDependency> GetAllPotentialDependencies() {
      return idsByMemberName.Values.SelectMany(x => x.Deps);
    }

    // The "id" attribute on a Boogie AST node is used by Boogie to label
    // that AST node in the SMT-Lib formula when constructing a verification
    // condition.
    private const string idAttributeName = "id";

    public void AddProofDependencyId(ICarriesAttributes boogieNode, IOrigin tok, ProofDependency dep) {
      var idString = GetProofDependencyId(dep);
      boogieNode.Attributes =
        new QKeyValue(tok, idAttributeName, new List<object>() { idString }, boogieNode.Attributes);
    }

    public ProofDependency GetFullIdDependency(TrackedNodeComponent component) {
      if (component is TrackedCallRequiresGoal requiresGoal) {
        var reqId = ProofDependenciesById[requiresGoal.requiresId];
        var callId = ProofDependenciesById[requiresGoal.callId];
        return new CallRequiresDependency((CallDependency)callId, (RequiresDependency)reqId);
      } else if (component is TrackedCallRequiresAssumed requiresAssumed) {
        var reqId = ProofDependenciesById[requiresAssumed.requiresId];
        var callId = ProofDependenciesById[requiresAssumed.callId];
        return new CallRequiresDependency((CallDependency)callId, (RequiresDependency)reqId);
      } else if (component is TrackedCallEnsures callEnsures) {
        var ensId = ProofDependenciesById[callEnsures.ensuresId];
        var callId = ProofDependenciesById[callEnsures.callId];
        return new CallEnsuresDependency((CallDependency)callId, (EnsuresDependency)ensId);
      } else if (component is TrackedInvariantEstablished invariantEstablished) {
        return ProofDependenciesById[invariantEstablished.invariantId];
      } else if (component is TrackedInvariantMaintained invariantMaintained) {
        return ProofDependenciesById[invariantMaintained.invariantId];
      } else if (component is TrackedInvariantAssumed invariantAssumed) {
        return ProofDependenciesById[invariantAssumed.invariantId];
      } else if (component is LabeledNodeComponent labeledNodeComponent) {
        return ProofDependenciesById[labeledNodeComponent.SolverLabel];
      } else {
        throw new ArgumentException($"Malformed dependency ID: {component.SolverLabel}");
      }
    }

    public IEnumerable<ProofDependency> GetOrderedFullDependencies(IEnumerable<TrackedNodeComponent> components) {
      return components
        .Select(GetFullIdDependency)
        .OrderBy(dep => dep.Range)
        .ThenBy(dep => dep.Description);
    }
  }
}