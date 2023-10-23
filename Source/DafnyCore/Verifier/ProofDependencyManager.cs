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
using Dafny;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Boogie;
using DafnyCore.Verifier;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public class ProofDependencyManager {
    // proof dependency tracking state
    public Dictionary<string, ProofDependency> ProofDependenciesById { get; } = new();
    private Dictionary<string, HashSet<ProofDependency>> idsByMemberName = new();
    private UInt64 proofDependencyIdCount = 0;
    private string currentDefinition = null;

    public string GetProofDependencyId(ProofDependency dep) {
      var idString = $"id{proofDependencyIdCount}";
      ProofDependenciesById[idString] = dep;
      proofDependencyIdCount++;
      if (!idsByMemberName.TryGetValue(currentDefinition, out var currentSet)) {
        currentSet = new HashSet<ProofDependency>();
        idsByMemberName[currentDefinition] = currentSet;
      }
      currentSet.Add(dep);
      return idString;
    }

    public void SetCurrentDefinition(string defName) {
      currentDefinition = defName;
    }

    public IEnumerable<ProofDependency> GetPotentialDependenciesForDefinition(string defName) {
      return idsByMemberName[defName];
    }

    public IEnumerable<ProofDependency> GetAllPotentialDependencies() {
      return idsByMemberName.Values.SelectMany(deps => deps);
    }

    // The "id" attribute on a Boogie AST node is used by Boogie to label
    // that AST node in the SMT-Lib formula when constructing a verification
    // condition.
    private const string idAttributeName = "id";

    public void AddProofDependencyId(ICarriesAttributes boogieNode, IToken tok, ProofDependency dep) {
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
  }
}