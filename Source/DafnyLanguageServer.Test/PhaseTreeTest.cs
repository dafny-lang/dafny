using System;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class PhaseTreeTest {

  record Root(int Index) : IPhase {
    public IPhase MaybeParent => null;
  }

  record HasParent(IPhase Parent, int Index) : IPhase {
    public IPhase MaybeParent => Parent;
  }

  [Fact]
  public void Add() {
    var tree = PhaseTree.Empty();

    var p0 = new Root(0);
    var p1 = new Root(0);
    var p000 = new HasParent(new HasParent(p0, 0), 0);
    var p01 = new HasParent(p0, 1);
    var p010 = new HasParent(p01, 0);
    tree = tree.Add(p000, Array.Empty<FileDiagnostic>());
    tree = tree.Add(p010, Array.Empty<FileDiagnostic>());
    tree = tree.Add(p1, Array.Empty<FileDiagnostic>());
    tree = tree.ClearDiagnosticsAndPruneChildren(null, new[] { p0 });
    tree = tree.Remove(p01);
  }
}