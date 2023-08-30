//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Boogie;
using DafnyCore.Verifier;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public class ProofDependencyManager {
    // proof dependency tracking state
    public Dictionary<string, ProofDependency> ProofDependenciesById { get; } = new();
    private UInt64 proofDependencyIdCount = 0;

    public string GetProofDependencyId(ProofDependency dep) {
      var idString = $"id{proofDependencyIdCount}";
      ProofDependenciesById[idString] = dep;
      proofDependencyIdCount++;
      return idString;
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

    // This suffix indicates that an ID string represents the assumption of
    // a specific ensures clause after a specific call.
    private const string ensuresSuffix = "$ensures";

    // This suffix indicates that an ID string represents the goal of
    // proving a specific requires clause before a specific call.
    private const string requiresSuffix = "$requires";

    // This suffix indicates that an ID string represents the assumption
    // of a specific requires clause after a specific call.
    private const string requiresAssumedSuffix = "$requires_assumed";

    // This suffix indicates that an ID string represents the goal of
    // proving that a specific loop invariant is established.
    private const string establishedSuffix = "$established";

    // This suffix indicates that an ID string represents the goal of
    // proving that a specific loop invariant is maintained.
    private const string maintainedSuffix = "$maintained";

    // This suffix indicates that an ID string represents the asssumption
    // of a specific loop invariant in the body of the loop.
    private const string assumeInBodySuffix = "$assume_in_body";

    // Get the full ProofDependency indicated by a compound ID string. These strings are
    // returned by the SMT solver to indicate which sub-formulas it used in constructing
    // a proof of a particular goal (more technically, the UNSAT core of the negation of
    // the goal). Because SMT-Lib only accepts strings as labels, we need to embed some
    // extra information in those strings to represent ways in which the original Boogie
    // commands and expressions are transformed and duplicated during Boogie's VC
    // generation process.
    public ProofDependency GetFullIdDependency(string idString) {
      var parts = idString.Split('$');
      if (idString.EndsWith(requiresSuffix) && parts.Length == 3) {
        var reqId = ProofDependenciesById[parts[0]];
        var callId = ProofDependenciesById[parts[1]];
        return new CallRequiresDependency((CallDependency)callId, (RequiresDependency)reqId);
      } else if (idString.EndsWith(requiresAssumedSuffix) && parts.Length == 3) {
        var reqId = ProofDependenciesById[parts[0]];
        var callId = ProofDependenciesById[parts[1]];
        return new CallRequiresDependency((CallDependency)callId, (RequiresDependency)reqId);
      } else if (idString.EndsWith(ensuresSuffix) && parts.Length == 3) {
        var ensId = ProofDependenciesById[parts[0]];
        var callId = ProofDependenciesById[parts[1]];
        return new CallEnsuresDependency((CallDependency)callId, (EnsuresDependency)ensId);
      } else if (idString.EndsWith(establishedSuffix) && parts.Length == 2) {
        return ProofDependenciesById[parts[0]];
      } else if (idString.EndsWith(maintainedSuffix) && parts.Length == 2) {
        return ProofDependenciesById[parts[0]];
      } else if (idString.EndsWith(assumeInBodySuffix) && parts.Length == 2) {
        return ProofDependenciesById[parts[0]];
      } else if (parts.Length > 1) {
        throw new ArgumentException($"Malformed dependency ID string: {idString}");
      } else {
        return ProofDependenciesById[idString];
      }
    }
  }
}