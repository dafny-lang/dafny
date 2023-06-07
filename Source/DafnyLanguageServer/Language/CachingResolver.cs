using System.Collections.Generic;
using System.Security.Cryptography;

namespace Microsoft.Dafny.LanguageServer.Language; 

public class CachingResolver : Resolver {
  
  private readonly PruneIfNotUsedSinceLastPruneCache<byte[], LiteralModuleDecl> resolutionCache = new(new HashEquality());
  private readonly Dictionary<LiteralModuleDecl, byte[]> hashes = new();

  public CachingResolver(DafnyOptions options) : base(options)
  {
  }

  public CachingResolver(Dafny.Program prog) : base(prog)
  {
  }

  protected override void ResolveModuleDeclaration(Dafny.Program prog, ModuleDecl decl, int beforeModuleResolutionErrorCount) {
    if (decl is LiteralModuleDecl literalModuleDecl) {
      hashes[literalModuleDecl] = DetermineHash(literalModuleDecl);
    }
    base.ResolveModuleDeclaration(prog, decl, beforeModuleResolutionErrorCount);
  }
  

  private byte[] DetermineHash(LiteralModuleDecl literal)
  {
    var moduleVertex = dependencies.FindVertex(literal);
    var hashAlgorithm = HashAlgorithm.Create("SHA256")!;
    hashAlgorithm.Initialize();
    foreach (var dependencyVertex in moduleVertex.Successors)
    {
      var dependency = dependencyVertex.N;
      if (dependency is LiteralModuleDecl literalDependency) {
        var dependencyHash = hashes[literalDependency];
        hashAlgorithm.TransformBlock(dependencyHash, 0, dependencyHash.Length, null, 0);
      }
    }

    var parseHash = literal.ModuleDef.UniqueParseContentHash.ToByteArray();
    hashAlgorithm.TransformFinalBlock(parseHash, 0, parseHash.Length);

    return hashAlgorithm.Hash!;
  }
}