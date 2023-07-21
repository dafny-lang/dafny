using System;
using System.Collections.Generic;
using System.IO;
using System.Security.Cryptography;
using System.Security.Policy;
using System.Text;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language;

public class CachingParser : ProgramParser {
  private readonly PruneIfNotUsedSinceLastPruneCache<byte[], DfyParseResult> parseCache = new(new HashEquality());

  public CachingParser(ILogger<ProgramParser> logger, IFileSystem fileSystem) : base(logger, fileSystem) {
  }

  public void Prune() {
    parseCache.Prune();
  }

  protected override DfyParseResult ParseFile(DafnyOptions options, TextReader reader, Uri uri) {
    var (newReader, hash) = ComputeHashFromReader(uri, reader, HashAlgorithm.Create("SHA256")!);
    if (!parseCache.TryGet(hash, out var result)) {
      logger.LogDebug($"Parse cache miss for {uri}");
      result = base.ParseFile(options, newReader, uri);
      parseCache.Set(hash, result);
    } else {
      logger.LogDebug($"Parse cache hit for {uri}");
    }

    // Clone declarations before returning them, since they are mutable and we don't want to mutate the one in the cache.
    // We should cache an immutable version of the AST instead: https://github.com/dafny-lang/dafny/issues/4086
    var cloner = new Cloner(true, false);
    var clonedResult = result! with {
      Module = new FileModuleDefinition(cloner, result.Module)
    };
    return clonedResult;
  }

  /// <summary>
  /// We read the contents of the reader and store them in memory using chunks
  /// to prevent allocating a large array of memory.
  /// </summary>
  private static (TextReader reader, byte[] hash) ComputeHashFromReader(Uri uri, TextReader reader, HashAlgorithm hashAlgorithm) {
    var result = new List<char[]>();
    const int chunkSize = 1024;
    hashAlgorithm.Initialize();
    // Add NUL delimiter to avoid collisions (otherwise hash("A" + "BC") == hash("AB" + "C"))
    var uriBytes = Encoding.UTF8.GetBytes(uri.ToString() + "\0");

    // We need to include the uri as part of the hash, because the parsed AST contains tokens that refer to the filename. 
    hashAlgorithm.TransformBlock(uriBytes, 0, uriBytes.Length, null, 0);
    while (true) {
      var chunk = new char[chunkSize];
      var readCount = reader.ReadBlock(chunk, 0, chunk.Length);
      if (readCount < chunk.Length) {
        var shortenedChunk = new char[readCount];
        Array.Copy(chunk, 0, shortenedChunk, 0, readCount);
        result.Add(shortenedChunk);
        var charArray = Encoding.UTF8.GetBytes(shortenedChunk);
        hashAlgorithm.TransformFinalBlock(charArray, 0, charArray.Length);
        return (new TextReaderFromCharArrays(result), hashAlgorithm.Hash!);
      } else {
        var charArray = Encoding.UTF8.GetBytes(chunk);
        hashAlgorithm.TransformBlock(charArray, 0, charArray.Length, null, 0);
      }
      result.Add(chunk);
    }
  }
}