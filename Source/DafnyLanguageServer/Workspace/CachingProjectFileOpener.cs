using System;
using System.CommandLine;
using System.Runtime.Caching;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Dafny;

public class CachingProjectFileOpener : ProjectFileOpener {
  public const int DefaultProjectFileCacheExpiryTime = 100;
  private readonly object nullRepresentative = new(); // Needed because you can't store null in the MemoryCache, but that's a value we want to cache.
  private readonly DafnyOptions serverOptions;
  private readonly MemoryCache projectFilePerFolderCache = new("projectFiles");


  static CachingProjectFileOpener() {
    OptionRegistry.RegisterOption(ProjectFileCacheExpiry, OptionScope.Cli);
  }

  public CachingProjectFileOpener(IFileSystem fileSystem, DafnyOptions serverOptions, IOrigin origin) : base(fileSystem, origin) {
    this.serverOptions = serverOptions;
  }

  public static readonly Option<int> ProjectFileCacheExpiry = new("--project-file-cache-expiry", () => DefaultProjectFileCacheExpiryTime,
    @"How many milliseconds the server will cache project file contents".TrimStart()) {
    IsHidden = true
  };

  protected override async Task<DafnyProject?> OpenProjectInFolder(string folderPath) {
    var cacheExpiry = serverOptions.Get(ProjectFileCacheExpiry);
    if (cacheExpiry == 0) {
      return await base.OpenProjectInFolder(folderPath);
    }

    var cachedResult = projectFilePerFolderCache.Get(folderPath);
    if (cachedResult != null) {
      return cachedResult == nullRepresentative ? null : ((DafnyProject?)cachedResult)?.Clone();
    }

    var result = await base.OpenProjectInFolder(folderPath);
    projectFilePerFolderCache.Set(new CacheItem(folderPath, (object?)result ?? nullRepresentative), new CacheItemPolicy {
      AbsoluteExpiration = new DateTimeOffset(DateTime.Now.Add(TimeSpan.FromMilliseconds(cacheExpiry)))
    });
    return result?.Clone();
  }
}