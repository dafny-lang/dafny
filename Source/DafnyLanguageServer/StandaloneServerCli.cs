using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using Serilog;
using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using OmniSharpLanguageServer = OmniSharp.Extensions.LanguageServer.Server.LanguageServer;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    public static async Task Main(string[] args) {
      var dafnyOptions = GetOptionsFromArgs(args);

      await Server.Start(dafnyOptions);
    }

    public static DafnyOptions GetOptionsFromArgs(string[] args) {
      var configuration = CreateConfiguration(args);

      var dafnyOptions = DafnyOptions.Create();

      var verifierOptions = new VerifierOptions();
      configuration.Bind(VerifierOptions.Section, verifierOptions);
      LineVerificationStatusOption.Instance.Set(dafnyOptions, verifierOptions.GutterStatus);
      VerificationTimeLimitOption.Instance.Set(dafnyOptions, verifierOptions.TimeLimit);
      CoresOption.Instance.Set(dafnyOptions, (int)verifierOptions.VcsCores);
      VerifySnapshotsOption.Instance.Set(dafnyOptions, verifierOptions.VerifySnapshots);

      var ghostOptions = new GhostOptions();
      configuration.Bind(GhostOptions.Section, ghostOptions);
      GhostIndicatorsOption.Instance.Set(dafnyOptions, ghostOptions.MarkStatements);

      var documentOptions = new DocumentOptions();
      configuration.Bind(DocumentOptions.Section, documentOptions);
      VerificationOption.Instance.Set(dafnyOptions, documentOptions.Verify);

      var pluginOptions = new DafnyPluginsOptions();
      configuration.Bind(DafnyPluginsOptions.Section, pluginOptions);
      PluginOption.Instance.Set(dafnyOptions, pluginOptions.Plugins.ToList());
      return dafnyOptions;
    }

    private static IConfiguration CreateConfiguration(string[] args) {
      return new ConfigurationBuilder()
        .AddCommandLine(args)
        .Build();
    }
  }
}
