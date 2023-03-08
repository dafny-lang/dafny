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
      var dafnyOptions = GetOptionsFromArgs(Console.Out, args);

      await Server.Start(dafnyOptions);
    }

    public static DafnyOptions GetOptionsFromArgs(TextWriter outWriter, string[] args) {
      var configuration = CreateConfiguration(args);

      var dafnyOptions = DafnyOptions.Create(outWriter);

      var verifierOptions = new VerifierOptions();
      configuration.Bind(VerifierOptions.Section, verifierOptions);
      dafnyOptions.Set(ServerCommand.LineVerificationStatus, verifierOptions.GutterStatus);
      dafnyOptions.Set(BoogieOptionBag.VerificationTimeLimit, verifierOptions.TimeLimit);
      dafnyOptions.Set(BoogieOptionBag.Cores, verifierOptions.VcsCores);
      dafnyOptions.Set(ServerCommand.VerifySnapshots, verifierOptions.VerifySnapshots);

      var ghostOptions = new GhostOptions();
      configuration.Bind(GhostOptions.Section, ghostOptions);
      dafnyOptions.Set(ServerCommand.GhostIndicators, ghostOptions.MarkStatements);

      var documentOptions = new DocumentOptions();
      configuration.Bind(DocumentOptions.Section, documentOptions);
      var mode = documentOptions.Verify switch {
        AutoVerification.Never => VerifyOnMode.Never,
        AutoVerification.OnChange => VerifyOnMode.Change,
        AutoVerification.OnSave => VerifyOnMode.Save,
        _ => throw new ArgumentOutOfRangeException()
      };
      dafnyOptions.Set(ServerCommand.Verification, mode);

      var pluginOptions = new DafnyPluginsOptions();
      configuration.Bind(DafnyPluginsOptions.Section, pluginOptions);
      dafnyOptions.Set(CommonOptionBag.Plugin, pluginOptions.Plugins.ToList());
      return dafnyOptions;
    }

    private static IConfiguration CreateConfiguration(string[] args) {
      return new ConfigurationBuilder()
        .AddCommandLine(args)
        .Build();
    }
  }
}
