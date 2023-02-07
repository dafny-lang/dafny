namespace Microsoft.Dafny.Compilers;

internal class InternalCompilersPluginConfiguration : Plugins.PluginConfiguration {
  public static readonly InternalCompilersPluginConfiguration Singleton = new();

  public override Plugins.IExecutableBackend[] GetCompilers() {
    return new Plugins.IExecutableBackend[] {
      new CsharpBackend(),
      new JavaScriptBackend(),
      new GoBackend(),
      new JavaBackend(),
      new PythonBackend(),
      new CppCompilerBackend(),
      new DafnyBackend()
    };
  }
}