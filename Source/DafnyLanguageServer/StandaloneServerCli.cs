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
using Microsoft.Extensions.DependencyInjection;
using OmniSharpLanguageServer = OmniSharp.Extensions.LanguageServer.Server.LanguageServer;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    public static async Task Main(string[] args) {
      var configuration = CreateConfiguration(args);
      var verifierOptions = configuration.Get<VerifierOptions>();
      var dafnyOptions = DafnyOptions.Create();
      LineVerificationStatusOption.Instance.Set(dafnyOptions, verifierOptions.GutterStatus);
      VerificationTimeLimitOption.Instance.Set(dafnyOptions, verifierOptions.TimeLimit);
      CoresOption.Instance.Set(dafnyOptions, (int)verifierOptions.VcsCores);
      VerifySnapshotsOption.Instance.Set(dafnyOptions, verifierOptions.VerifySnapshots);
      
      var ghostOptions = configuration.Get<GhostOptions>();
      GhostIndicatorsOption.Instance.Set(dafnyOptions, ghostOptions.MarkStatements);
      
      var pluginOptions = configuration.Get<DafnyPluginsOptions>();
      PluginOption.Instance.Set(dafnyOptions, pluginOptions.Plugins.ToList());
      
      await Server.Start(dafnyOptions);
    }
    
    private static IConfiguration CreateConfiguration(string[] args) {
      return new ConfigurationBuilder()
        .AddJsonFile("DafnyLanguageServer.appsettings.json", optional: true)
        .AddCommandLine(args)
        .Build();
    }
  }
}
