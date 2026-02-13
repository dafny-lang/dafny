using System;
using System.Collections.Generic;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

[Collection("Sequential Collection")]
public class ProjectManagerDatabaseTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task CloseAndReopenProject() {
    var path = GetFreshTempPath();
    var project = CreateAndOpenTestDocument("", Path.Combine(path, DafnyProject.FileName));
    var file1 = CreateAndOpenTestDocument("method Foo() { }", Path.Combine(path, "file1.dfy"));

    client.CloseDocument(project);
    var project2 = CreateAndOpenTestDocument("", Path.Combine(path, DafnyProject.FileName));
    ApplyChange(ref file1, new Range(0, 0, 0, 0), @"syntaxError");
    var error = await GetLastDiagnostics(file1);
    Assert.NotEmpty(error);
  }

  [Fact]
  public async Task ChangeAndUndoProjectWithMultipleFiles() {
    var path = GetFreshTempPath();
    var project = CreateAndOpenTestDocument("", Path.Combine(path, DafnyProject.FileName));
    var file1 = CreateAndOpenTestDocument("method Foo() { }", Path.Combine(path, "file1.dfy"));
    var file2 = CreateAndOpenTestDocument("method Bar() { }", Path.Combine(path, "file2.dfy"));

    ApplyChange(ref project, new Range(0, 0, 0, 0), @"includes = [""**/*.dfy""]
");
    ApplyChange(ref file1, new Range(0, 0, 0, 0), @"//comment\n");
    ApplyChange(ref project, new Range(0, 0, 1, 0), "");
    var fine = await GetLastDiagnostics(project);
    ApplyChange(ref file2, new Range(0, 0, 0, 0), @"syntaxError");
    var error = await GetLastDiagnostics(file2);
    Assert.NotEmpty(error);
  }

  [Fact]
  public async Task OpenAndCloseConcurrentlySeparateProjects() {
    int documentsToLoadConcurrently = 50;
    var source = "// comment";
    var loadingDocuments = new List<TextDocumentItem>();
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      var documentItem = await CreateOpenAndWaitForResolve(source, $"pmdtest1_{i}.dfy");
      loadingDocuments.Add(documentItem);
    }

    List<Task> tasks = [];
    foreach (var loadingDocument in loadingDocuments) {
      // Mix regular and close requests, both can be handled in parallel, although the hover might fail for a closed document.
      tasks.Add(client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = loadingDocument.Uri }, CancellationToken));
      client.CloseDocument(loadingDocument);
    }

    await Task.WhenAll(tasks);
  }

  [Fact]
  public async Task ConcurrentProjectMigration() {
    int documentsToLoadConcurrently = 50;
    var source = "// comment";
    var loadingDocuments = new List<TextDocumentItem>();
    var directory = Path.GetRandomFileName();
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      var documentItem = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, $"nested{i}/pmdtest2.dfy"));
      loadingDocuments.Add(documentItem);
    }

    // Create a project file for each test document.
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      await CreateOpenAndWaitForResolve("", Path.Combine(directory, $"nested{i}/{DafnyProject.FileName}"));
    }

    // Concurrently migrate projects
    List<Task> tasks = [];
    foreach (var loadingDocument in loadingDocuments) {
      // By doing a regular request, learn that the file's project has changed.
      tasks.Add(client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = loadingDocument.Uri }, CancellationToken));
    }

    await Task.WhenAll(tasks);
  }


  [Fact]
  public async Task OpenAndCloseConcurrentlySameProject() {
    int documentsToLoadConcurrently = 50;
    var source = "// comment";
    var loadingDocuments = new List<TextDocumentItem>();
    var directory = Path.GetRandomFileName();
    var project = CreateTestDocument("", Path.Combine(directory, DafnyProject.FileName));
    client.OpenDocument(project);
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      var documentItem = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, $"pmdtest3_{i}.dfy"));
      loadingDocuments.Add(documentItem);
    }

    List<Task> tasks = [];
    foreach (var loadingDocument in loadingDocuments) {
      tasks.Add(client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = loadingDocument.Uri }, CancellationToken));
      client.CloseDocument(loadingDocument);
    }

    await Task.WhenAll(tasks);
  }

  public ProjectManagerDatabaseTest(ITestOutputHelper output) : base(output) {
  }
}