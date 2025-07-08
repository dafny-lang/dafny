using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;
using Dafny.Plugins;

public interface Plugin {
  public IEnumerable<IExecutableBackend> GetCompilers(DafnyOptions options);
  public IEnumerable<IRewriter> GetRewriters(ErrorReporter reporter);
  public IEnumerable<DocstringRewriter> GetDocstringRewriters(DafnyOptions options);
  public IEnumerable<CompilerInstrumenter> GetCompilerInstrumenters(ErrorReporter reporter);
}

record ErrorPlugin(string AssemblyAndArgument, Exception Exception) : Plugin {
  public IEnumerable<IExecutableBackend> GetCompilers(DafnyOptions options) {
    return [];
  }

  public IEnumerable<IRewriter> GetRewriters(ErrorReporter reporter) {
    return new[] { new ErrorRewriter(reporter, this) };
  }

  public IEnumerable<DocstringRewriter> GetDocstringRewriters(DafnyOptions options) {
    return [];
  }

  public IEnumerable<CompilerInstrumenter> GetCompilerInstrumenters(ErrorReporter reporter) {
    return [];
  }

  class ErrorRewriter : IRewriter {
    private readonly ErrorPlugin errorPlugin;

    public ErrorRewriter(ErrorReporter reporter, ErrorPlugin errorPlugin) : base(reporter) {
      this.errorPlugin = errorPlugin;
    }

    internal override void PreResolve(Program program) {
      program.Reporter.Error(MessageSource.Resolver, Token.NoToken, $"Error while instantiating plugin '{errorPlugin.AssemblyAndArgument}':\n{errorPlugin.Exception}");
      base.PreResolve(program);
    }
  }
}

public class ConfiguredPlugin : Plugin {
  public PluginConfiguration Configuration { get; }

  public ConfiguredPlugin(PluginConfiguration configuration) {
    Configuration = configuration;
  }

  public IEnumerable<IExecutableBackend> GetCompilers(DafnyOptions options) {
    return Configuration.GetCompilers(options);
  }

  public IEnumerable<IRewriter> GetRewriters(ErrorReporter reporter) {
    return Configuration.GetRewriters(reporter).Select(rewriter => new PluginRewriter(reporter, rewriter));
  }

  public IEnumerable<DocstringRewriter> GetDocstringRewriters(DafnyOptions options) {
    return Configuration.GetDocstringRewriters(options);
  }

  public IEnumerable<CompilerInstrumenter> GetCompilerInstrumenters(ErrorReporter reporter) {
    return Configuration.GetCompilerInstrumenters(reporter);
  }
}

/// <summary>
/// This class wraps an assembly and an extracted configuration from this assembly,
/// The configuration provides the methods to parse command-line arguments and obtain Rewriters 
/// </summary>
public class AssemblyPlugin : ConfiguredPlugin {
  public AssemblyPlugin(Assembly assembly, string[] args) : base(LoadConfiguration(assembly, args)) {
  }

  public static Plugin Load(string pluginPath, string[] args) {
    return new AssemblyPlugin(Assembly.LoadFrom(pluginPath), args);
  }

  class AutomaticPluginConfiguration : PluginConfiguration {
    public AutomaticPluginConfiguration(Assembly assembly) {
      var types = assembly.GetTypes();

      Rewriters = FindPluginComponents<Rewriter, Func<ErrorReporter, Rewriter>>(assembly, CreateRewriterFactory);
      Compilers = FindPluginComponents<IExecutableBackend, Func<IExecutableBackend>>(assembly, CreateCompilerFactory);
      CompilerInstrumenters = FindPluginComponents<CompilerInstrumenter, Func<ErrorReporter, CompilerInstrumenter>>(assembly, CreateCompilerInstrumenterFactory);

      // Report an error if this assembly doesn't contain any plugins.  We only
      // get to this point if we have not found a `PluginConfiguration` either,
      // so no need to check for one here.
      if (Rewriters.Length == 0 && Compilers.Length == 0 && CompilerInstrumenters.Length == 0) {
        throw new Exception($"Plugin {assembly.Location} does not contain any supported plugin classes.  " +
                            "Expecting one of the following:\n" +
                            $"- ${typeof(Plugins.Rewriter).FullName}\n" +
                            $"- ${typeof(Plugins.IExecutableBackend).FullName}\n" +
                            $"- ${typeof(Plugins.CompilerInstrumenter).FullName}\n" +
                            $"- ${typeof(Plugins.PluginConfiguration).FullName}");
      }
    }

    private TFactory[] FindPluginComponents<TSource, TFactory>(Assembly assembly, Func<System.Type, TFactory> createFactory) {
      return assembly.GetTypes()
          .Where(type => type.IsAssignableTo(typeof(TSource)))
          .Select(createFactory).ToArray();
    }

    private Func<ErrorReporter, Rewriter>[] Rewriters { get; init; }
    Func<ErrorReporter, Rewriter> CreateRewriterFactory(System.Type type) =>
      errorReporter => (Rewriter)Activator.CreateInstance(type, errorReporter);

    private Func<IExecutableBackend>[] Compilers { get; init; }

    private Func<ErrorReporter, CompilerInstrumenter>[] CompilerInstrumenters { get; init; }

    Func<IExecutableBackend> CreateCompilerFactory(System.Type type) =>
      () => (IExecutableBackend)Activator.CreateInstance(type);

    Func<ErrorReporter, CompilerInstrumenter> CreateCompilerInstrumenterFactory(System.Type type) =>
      errorReporter => (CompilerInstrumenter)Activator.CreateInstance(type, errorReporter);

    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) =>
      Rewriters.Select(funcErrorReporterRewriter =>
        funcErrorReporterRewriter(errorReporter)).ToArray();

    public override IExecutableBackend[] GetCompilers(DafnyOptions options) =>
      Compilers.Select(c => c()).ToArray();

    public override CompilerInstrumenter[] GetCompilerInstrumenters(ErrorReporter reporter) =>
      CompilerInstrumenters.Select(c => c(reporter)).ToArray();
  }

  public static IEnumerable<System.Type> GetConfigurationsTypes(Assembly assembly) {
    return assembly.GetTypes()
      .Where(type => type.IsAssignableTo(typeof(PluginConfiguration)));
  }

  private static PluginConfiguration LoadConfiguration(Assembly assembly, string[] args) {
    PluginConfiguration pluginConfiguration = null;
    foreach (var configurationType in GetConfigurationsTypes(assembly)) {
      if (pluginConfiguration != null) {
        throw new Exception(
          $"Only one class should extend Microsoft.Dafny.Plugins.PluginConfiguration from {assembly.Location}. Please remove {configurationType}.");
      }

      pluginConfiguration = (PluginConfiguration)Activator.CreateInstance(configurationType);

      if (pluginConfiguration == null) {
        throw new Exception($"Could not instantiate a {configurationType} from {assembly.Location}");
      }

      pluginConfiguration.ParseArguments(args);
    }

    pluginConfiguration ??= new AutomaticPluginConfiguration(assembly);
    return pluginConfiguration;
  }

}
