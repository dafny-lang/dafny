using System;
using System.Collections.Concurrent;
using System.IO;
using System.Linq;
using DafnyCore.Options;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class LanguageServerFilesystem : IFileSystem {
  private readonly ILogger<LanguageServerFilesystem> logger;

  public LanguageServerFilesystem(ILogger<LanguageServerFilesystem> logger) {
    this.logger = logger;
  }

  private class Entry {
    public TextBuffer Buffer { get; set; }
    public int? Version { get; set; }

    public Entry(TextBuffer buffer, int? version) {
      Buffer = buffer;
      Version = version;
    }
  }

  private readonly ConcurrentDictionary<Uri, Entry> openFiles = new();

  public bool OpenDocument(TextDocumentItem document) {
    logger.LogDebug($"Opening file {document.Uri}");
    var uri = document.Uri.ToUri();
    if (openFiles.ContainsKey(uri)) {
      throw new InvalidOperationException($"Cannot open file {uri} because it is already open");
    }

    string existingText = "";
    try {
      if (OnDiskFileSystem.Instance.Exists(uri)) {
        using var fileStream = OnDiskFileSystem.Instance.ReadFile(uri).Reader;
        existingText = fileStream.ReadToEnd();
      }
    } catch (IOException) {
      // If we don't manage to detect whether this document already existed ond disc,
      // that only triggers a performance penalty
    }
    openFiles[uri] = new Entry(new TextBuffer(document.Text), document.Version);
    return existingText != document.Text;
  }

  public bool UpdateDocument(DidChangeTextDocumentParams documentChange) {
    var uri = documentChange.TextDocument.Uri.ToUri();
    if (!openFiles.TryGetValue(uri, out var entry)) {
      throw new InvalidOperationException("Cannot update file that has not been opened");
    }

    var buffer = entry.Buffer;
    var mergedBuffer = buffer;
    try {
      foreach (var change in documentChange.ContentChanges) {
        mergedBuffer = mergedBuffer.ApplyTextChange(change);
      }
    } catch (ArgumentOutOfRangeException) {
      return false;
    }

    // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
    // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
    var oldVer = entry.Version;
    var newVersion = documentChange.TextDocument.Version;
    var documentUri = documentChange.TextDocument.Uri;
    if (oldVer >= newVersion) {
      throw new InvalidOperationException(
        $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVersion}");
    }

    // We assume no concurrent mutating calls to IFileSysten, in particular to OpenDocument and UpdateDocument
    // Otherwise we'd have to lock around these calls.
    openFiles[uri] = new Entry(mergedBuffer, newVersion!.Value);
    return true;
  }

  public void CloseDocument(TextDocumentIdentifier document) {
    var uri = document.Uri.ToUri();

    logger.LogDebug($"Closing document {document.Uri}");
    if (!openFiles.TryRemove(uri, out _)) {
      logger.LogError($"Could not close file {uri} because it was not open.");
    }
  }

  public TextBuffer? GetBuffer(Uri uri) {
    if (openFiles.TryGetValue(uri, out var entry)) {
      return entry.Buffer;
    }

    return null;
  }

  public FileSnapshot ReadFile(Uri uri) {
    if (openFiles.TryGetValue(uri, out var entry)) {
      return new FileSnapshot(new StringReader(entry.Buffer.Text), entry.Version);
    }

    return OnDiskFileSystem.Instance.ReadFile(uri);
  }

  public bool Exists(Uri path) {
    return openFiles.ContainsKey(path) || OnDiskFileSystem.Instance.Exists(path);
  }

  public DirectoryInfoBase GetDirectoryInfoBase(string root) {
    var inMemoryFiles = openFiles.Keys.Select(openFileUri => openFileUri.LocalPath);
    var inMemory = new InMemoryDirectoryInfoFromDotNet8(root, inMemoryFiles);

    return new CombinedDirectoryInfo(new[] { inMemory, OnDiskFileSystem.Instance.GetDirectoryInfoBase(root) });
  }
}