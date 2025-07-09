﻿using System;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie.SMTLib;
using Action = System.Action;

namespace Microsoft.Dafny.LanguageServer {
  public static class DafnyLanguageServer {
    private static string DafnyVersion {
      get {
        var version = typeof(DafnyLanguageServer).Assembly.GetName().Version!;
        return $"{version.Major}.{version.Minor}.{version.Build}.{version.Revision}";
      }
    }

    public static LanguageServerOptions WithDafnyLanguageServer(this LanguageServerOptions options, DafnyOptions dafnyOptions, Action killLanguageServer) {
      options.ServerInfo = new ServerInfo {
        Name = "Dafny",
        Version = DafnyVersion
      };
      return options
        .WithDafnyLanguage()
        .WithDafnyWorkspace()
        .WithDafnyHandlers(dafnyOptions)
        .OnInitialize((server, @params, token) => InitializeAsync(server, @params, token, killLanguageServer))
        .OnStarted(StartedAsync);
    }

    private static Task InitializeAsync(ILanguageServer server, InitializeParams request, CancellationToken cancelRequestToken,
        Action killLanguageServer) {
      var logger = server.GetRequiredService<ILogger<LanguageServer>>();

      KillLanguageServerIfParentDies(logger, request, killLanguageServer);

      PublishSolverPath(server);

      return Task.CompletedTask;
    }

    private static readonly Regex Z3VersionRegex = new Regex(@"Z3 version (?<major>\d+)\.(?<minor>\d+)\.(?<patch>\d+)");

    private static void PublishSolverPath(ILanguageServer server) {
      var telemetryPublisher = server.GetRequiredService<TelemetryPublisherBase>();
      var options = server.GetRequiredService<DafnyOptions>();
      string solverPath;
      try {
        var proverOptions = new SMTLibSolverOptions(options);
        proverOptions.Parse(options.ProverOptions);
        if (proverOptions.ProverName == "noop") {
          telemetryPublisher.PublishSolverPath("noop solver");
          return;
        }
        solverPath = proverOptions.ExecutablePath();
        HandleZ3Version(telemetryPublisher, solverPath);
      } catch (Exception e) {
        solverPath = $"Error while determining solver path: {e}";
      }

      telemetryPublisher.PublishSolverPath(solverPath);
    }

    private static void HandleZ3Version(TelemetryPublisherBase telemetryPublisher, string solverPath) {
      var z3Version = DafnyOptions.GetZ3Version(solverPath);
      if (z3Version is null) {
        return;
      }

      telemetryPublisher.PublishZ3Version($"Z3 version {z3Version}");
    }

    /// <summary>
    /// As part of the LSP spec, a language server must kill itself if its parent process dies
    /// https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1713
    /// </summary>
    private static void KillLanguageServerIfParentDies(ILogger<LanguageServer> logger, InitializeParams request,
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
      server.SendNotification("serverStarted", new[] { DafnyVersion });
      server.SendNotification("dafnyLanguageServerVersionReceived", new[] { DafnyVersion });
      return Task.CompletedTask;
    }
  }
}
