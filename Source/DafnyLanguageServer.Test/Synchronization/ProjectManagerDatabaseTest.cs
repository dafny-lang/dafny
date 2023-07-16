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

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization; 

public class ProjectManagerDatabaseTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task OpenAndCloseConcurrentlySeparateProjects() {
    int documentsToLoadConcurrently = 50;
    var source = "// comment";
    var loadingDocuments = new List<TextDocumentItem>();
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      var documentItem = CreateTestDocument(source, $"test_{i}.dfy");
      client.OpenDocument(documentItem);
      loadingDocuments.Add(documentItem);
    }

    List<Task> tasks = new();
    foreach (var loadingDocument in loadingDocuments) {
      // Mix regular and close requests, both can be handled in parallel.
      tasks.Add(client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = loadingDocument.Uri }, CancellationToken));
      tasks.Add(client.CloseDocumentAndWaitAsync(loadingDocument, CancellationToken));
    }
    foreach (var _ in loadingDocuments) {
      await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      // They either have a File contains no code diagnostics or no diagnostics if parsing failed to happen due 
      // to the file already having been closed.
    }

    await Task.WhenAll(tasks);
  }

  [Fact]
  public async Task ConcurrentProjectMigration() {
    int documentsToLoadConcurrently = 50;
    var source = "// comment";
    var loadingDocuments = new List<TextDocumentItem>();
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      var documentItem = await CreateAndOpenTestDocument(source, $"nested{i}/test.dfy");
      loadingDocuments.Add(documentItem);
    }

    // Create a project file for each test document.
    for (int i = 0; i < documentsToLoadConcurrently; i++) {
      await CreateAndOpenTestDocument(source, $"nested{i}/{DafnyProject.FileName}");
    }

    // Concurrently migrate projects
    List<Task> tasks = new();
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
      var documentItem = CreateTestDocument(source, Path.Combine(directory, $"test_{i}.dfy"));
      client.OpenDocument(documentItem);
      loadingDocuments.Add(documentItem);
    }

    List<Task> tasks = new();
    foreach (var loadingDocument in loadingDocuments) {
      tasks.Add(client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = loadingDocument.Uri }, CancellationToken));
      tasks.Add(client.CloseDocumentAndWaitAsync(loadingDocument, CancellationToken));
    }
    foreach (var _ in loadingDocuments) {
      await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      // They either have a File contains no code diagnostics or no diagnostics if parsing failed to happen due 
      // to the file already having been closed.
    }

    await Task.WhenAll(tasks);
  }

  public ProjectManagerDatabaseTest(ITestOutputHelper output) : base(output) {
  }
}