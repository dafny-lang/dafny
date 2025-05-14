using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny.Compilers;

internal class InternalBackendsPluginConfiguration : Plugins.PluginConfiguration {
  public static readonly InternalBackendsPluginConfiguration Singleton = new();

  public override IExecutableBackend[] GetCompilers(DafnyOptions options) {
    return [
      new CsharpBackend(options),
      new LibraryBackend(options),
      new ResolvedDesugaredExecutableDafnyBackend(options)
    ];
  }
}