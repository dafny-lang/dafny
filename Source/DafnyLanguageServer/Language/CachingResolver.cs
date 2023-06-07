using System.Collections.Generic;
using System.Security.Cryptography;

namespace Microsoft.Dafny.LanguageServer.Language; 

/// <summary>
/// How do I get the cached Literal back into the AST ? Where is it even stored?
/// ModuleDecls can be part of the TopLevelDecls of other modules, so they're stored in the hierarchy
/// Are they also stored somewhere else, maybe in program?
/// Can I get rid of Program.ModuleSigs ???
/// Seems to relate to AbstractModuleDecl. What are they?
///
/// How do I know what pointers there are to a module? I guess that only until after a module resolves do we get outside pointers into it
/// Side effects of ResolveModuleDeclaration are also, or only?, to update ModuleSigs
/// 
/// I could have a Graph<Pointer<ModuleDecl>>
/// 
/// What's the purpose of ModuleBindings, how do I cache its update?
///
/// What's an alias module decl?
/// What's an abstract module decl?
/// </summary>
// public class CachingResolver : ProgramResolver {
//   
//   private readonly PruneIfNotUsedSinceLastPruneCache<byte[], LiteralModuleDecl> resolutionCache = new(new HashEquality());
//   private readonly Dictionary<LiteralModuleDecl, byte[]> hashes = new();
//
//   public CachingResolver(DafnyOptions options) : base(options)
//   {
//   }
//
//   public CachingResolver(Dafny.Program prog) : base(prog)
//   {
//   }
//
//   protected override void ResolveModuleDeclaration(Dafny.Program prog, ModuleDecl decl, int beforeModuleResolutionErrorCount) {
//     if (decl is LiteralModuleDecl literalModuleDecl) {
//       hashes[literalModuleDecl] = DetermineHash(literalModuleDecl);
//     }
//     base.ResolveModuleDeclaration(prog, decl, beforeModuleResolutionErrorCount);
//   }
//   
//
//   private byte[] DetermineHash(LiteralModuleDecl literal)
//   {
//     var moduleVertex = dependencies.FindVertex(literal);
//     var hashAlgorithm = HashAlgorithm.Create("SHA256")!;
//     hashAlgorithm.Initialize();
//     foreach (var dependencyVertex in moduleVertex.Successors)
//     {
//       var dependency = dependencyVertex.N;
//       if (dependency is LiteralModuleDecl literalDependency) {
//         var dependencyHash = hashes[literalDependency];
//         hashAlgorithm.TransformBlock(dependencyHash, 0, dependencyHash.Length, null, 0);
//       }
//     }
//
//     var parseHash = literal.ModuleDef.UniqueParseContentHash.ToByteArray();
//     hashAlgorithm.TransformFinalBlock(parseHash, 0, parseHash.Length);
//
//     return hashAlgorithm.Hash!;
//   }
// }