using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.DependencyInjection.Extensions;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer {
  public static class DafnyLanguageServer {
    private static List<string> loadErrors = new List<string>();
    public static IReadOnlyList<string> LoadErrors => loadErrors;
    private static string DafnyVersion {
      get {
        var version = typeof(DafnyLanguageServer).Assembly.GetName().Version!;
        return $"{version.Major}.{version.Minor}.{version.Build}.{version.Revision}";
      }
    }

    public static LanguageServerOptions WithDafnyLanguageServer(this LanguageServerOptions options,
        IConfiguration configuration, Action killLanguageServer) {
      return options
        .WithDafnyLanguage(configuration)
        .WithDafnyWorkspace(configuration)
        .WithDafnyHandlers()
        .OnInitialize((server, @params, token) => InitializeAsync(server, @params, token, killLanguageServer))
        .OnStarted(StartedAsync);
    }

    private static Task InitializeAsync(ILanguageServer server, InitializeParams request, CancellationToken cancelRequestToken,
        Action killLanguageServer) {
      var logger = server.GetRequiredService<ILogger<Program>>();
      logger.LogTrace("initializing service");

      LoadPlugins(logger, server);

      KillLanguageServerIfParentDies(logger, request, killLanguageServer);

      return Task.CompletedTask;
    }

    /// <summary>
    /// Load the plugins for the Dafny pipeline
    /// </summary>
    private static void LoadPlugins(ILogger<Program> logger, ILanguageServer server) {
      var dafnyPluginsOptions = server.GetRequiredService<IOptions<DafnyPluginsOptions>>();
      var lastPlugin = "";
      try {
        foreach (var pluginPathArgument in dafnyPluginsOptions.Value.Plugins) {
          lastPlugin = pluginPathArgument;
          DafnyOptions.O.Parse(new[] { "-plugin:" + pluginPathArgument });
        }
      } catch (Exception e) {
        logger.LogError(e, $"Error while instantiating plugin {lastPlugin}");
        loadErrors.Add($"Error while instantiating plugin {lastPlugin}. Please restart the server.\n" + e);
      }
    }

    /// <summary>
    /// As part of the LSP spec, a language server must kill itself if its parent process dies
    /// https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1713
    /// </summary>
    private static void KillLanguageServerIfParentDies(ILogger<Program> logger, InitializeParams request,
        Action killLanguageServer) {
      if (!(request.ProcessId >= 0)) {
        return;
      }

      void Kill() {
        logger.LogWarning("Shutting down language server because parent process died.");
        killLanguageServer();
      }

      try {
        var hostProcess = Process.GetProcessById((int)request.ProcessId);
        hostProcess.EnableRaisingEvents = true;
        hostProcess.Exited += (_, _) => Kill();
      } catch (ArgumentException) {
        // If the process dies before we get here then request shutdown immediately
        Kill();
      }
    }

    private static Task StartedAsync(ILanguageServer server, CancellationToken cancellationToken) {
      // TODO this currently only sent to get rid of the "Server answer pending" of the VSCode plugin.
      server.SendNotification("serverStarted", DafnyVersion);
      server.SendNotification("dafnyLanguageServerVersionReceived", DafnyVersion);
      return Task.CompletedTask;
    }
  }
}
