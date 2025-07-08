using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Security.Cryptography;
using System.Threading;
using System.Threading.Tasks;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language;

public class ResolutionCache {
  public PruneIfNotUsedSinceLastPruneCache<byte[], ModuleResolutionResult> Modules { get; } = new(new HashEquality());
  public SystemModuleManager? Builtins { get; set; }
  public Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>>? SystemClassMembers { get; set; }
}

public class CachingResolver : ProgramResolver {
  private readonly ILogger<CachingResolver> logger;
  private readonly Dictionary<ModuleDecl, byte[]> hashes = new();
  private readonly ResolutionCache cache;
  private readonly TelemetryPublisherBase telemetryPublisher;

  public CachingResolver(
    Program program,
    ILogger<CachingResolver> logger,
    TelemetryPublisherBase telemetryPublisher,
    ResolutionCache cache)
    : base(program) {
    this.logger = logger;
    this.cache = cache;
    this.telemetryPublisher = telemetryPublisher;
  }

  public override Task Resolve(CancellationToken cancellationToken) {
    return cache.Modules.ProfileAndPruneCache(async () => {
      await base.Resolve(cancellationToken);
      return Task.FromResult(Unit.Value);
    }, logger, telemetryPublisher, Program.FullName, "resolution", cancellationToken);
  }

  protected override Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> ResolveSystemModule(Program program) {
    if (cache.Builtins == null || !new HashEquality().Equals(cache.Builtins.MyHash, program.SystemModuleManager.MyHash)) {
      var systemClassMembers = base.ResolveSystemModule(program);
      cache.Builtins = program.SystemModuleManager;
      cache.SystemClassMembers = systemClassMembers;
      logger.LogDebug($"Resolution cache miss for system module");
    } else {
      program.SystemModuleManager = cache.Builtins;
      logger.LogDebug($"Resolution cache hit for system module");
    }

    return cache.SystemClassMembers!;
  }

  protected override ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl decl) {
    var hash = GetHash(decl);
    hashes[decl] = hash;

    if (!cache.Modules.TryGet(hash, out var result)) {
      logger.LogDebug($"Resolution cache miss for {decl}");
      var beforeResolution = DateTime.Now;
      result = base.ResolveModuleDeclaration(compilation, decl);
      cache.Modules.Set(hash, result);
      telemetryPublisher.PublishTime("ModuleResolution", decl.FullName, DateTime.Now - beforeResolution);
    } else {
      logger.LogDebug($"Resolution cache hit for {decl}");
    }
    return result!;
  }

  private byte[] GetHash(ModuleDecl moduleDeclaration) {
    if (!hashes.TryGetValue(moduleDeclaration, out var result)) {
      var moduleVertex = dependencies.FindVertex(moduleDeclaration);
      var hashAlgorithm = SHA256.Create()!;
      hashAlgorithm.Initialize();
      // We don't want the order of Successors to influence the hash, so we order by the content hash, for which CloneId is currently a proxy
      var orderedSuccessors = moduleVertex.Successors.OrderBy(s => s.N.CloneId);
      foreach (var dependencyVertex in orderedSuccessors) {
        var dependency = dependencyVertex.N;
        // DetermineHash is always called before 
        var dependencyHash = GetHash(dependency);
        hashAlgorithm.TransformBlock(dependencyHash, 0, dependencyHash.Length, null, 0);
      }

      hashAlgorithm.TransformBlock(cache.Builtins!.MyHash, 0, cache.Builtins!.MyHash.Length, null, 0);
      // Here we would like to use a hash of the contents of the module declaration, but we don't have that.
      // We use the CloneId as a defensive proxy for a content hash.
      // The CloneId stays unchanged if none of the files in which the module occurs have been changed.
      var parseHash = moduleDeclaration.CloneId.ToByteArray();
      hashAlgorithm.TransformFinalBlock(parseHash, 0, parseHash.Length);

      result = hashes[moduleDeclaration] = hashAlgorithm.Hash!;
    }

    return result;
  }
}
