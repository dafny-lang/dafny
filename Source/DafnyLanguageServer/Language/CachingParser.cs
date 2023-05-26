using System;
using System.Collections.Generic;
using System.IO;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language;

public class CachingParser : ProgramParser {
  private readonly TickingCache<byte[], DfyParseResult> parseCache = new(new ByteArrayEquality());
  private readonly ILogger<CachingParser> logger;

  public CachingParser(ILogger<CachingParser> logger) {
    this.logger = logger;
  }

  public void Tick() {
    parseCache.Tick();
  }
      
  protected override DfyParseResult ParseFile(DafnyOptions options, TextReader reader, Uri uri) {
    var (newReader, hash) = ComputeHashFromReader(reader, HashAlgorithm.Create("SHA256")!);
    if (!parseCache.TryGet(hash, out var result)) {
      logger.LogDebug($"Parse cache miss for {uri}");
      result = base.ParseFile(options, newReader, uri);
      parseCache.Set(hash, result);
    } else {
      logger.LogDebug("Parse cache hit");
    }

    return result!;
  }

  /// <summary>
  /// We read the contents of the reader and store them in memory using chunks,
  /// to prevent allocating a large array of memory.
  /// </summary>
  /// <param name="reader"></param>
  /// <param name="hashAlgorithm"></param>
  /// <returns></returns>
  private static (TextReader reader, byte[] hash) ComputeHashFromReader(TextReader reader, HashAlgorithm hashAlgorithm) {
    var result = new List<char[]>();
    const int chunkSize = 1024;
    hashAlgorithm.Initialize();
    while (true) {
      var chunk = new char[chunkSize];
      var readCount = reader.ReadBlock(chunk, 0, chunk.Length);
      if (readCount < chunk.Length) {
        var shortenedChunk = new char[readCount];
        Array.Copy(chunk, 0, shortenedChunk, 0, readCount);
        result.Add(shortenedChunk);
        var charArray = Encoding.UTF8.GetBytes(shortenedChunk);
        var hash = hashAlgorithm.TransformFinalBlock(charArray, 0, charArray.Length);
        return (new ReaderFromCharArrays(result), hash);
      } else {
        var charArray = Encoding.UTF8.GetBytes(chunk);
        hashAlgorithm.TransformBlock(charArray, 0, charArray.Length, null, 0);
      }
      result.Add(chunk);
    }
  }
}