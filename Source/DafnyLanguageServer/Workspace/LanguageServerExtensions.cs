﻿using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Extension methods to register the dafny workspace services to the language server implementation.
  /// </summary>
  public static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny workspace.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <param name="configuration">The configuration object holding the server configuration.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyWorkspace(this LanguageServerOptions options) {
      return options.WithServices(services => services.WithDafnyWorkspace());
    }

    private static IServiceCollection WithDafnyWorkspace(this IServiceCollection services) {
      return services
        .AddSingleton<IProjectDatabase, ProjectManagerDatabase>()
        .AddSingleton<CreateProjectManager>(provider => (scheduler, cache, documentIdentifier) => new ProjectManager(
          provider.GetRequiredService<DafnyOptions>(),
          provider.GetRequiredService<ILogger<ProjectManager>>(),
          provider.GetRequiredService<CreateMigrator>(),
          provider.GetRequiredService<IFileSystem>(),
          provider.GetRequiredService<TelemetryPublisherBase>(),
          provider.GetRequiredService<IProjectDatabase>(),
          provider.GetRequiredService<CreateCompilation>(),
          provider.GetRequiredService<CreateIdeStateObserver>(),
          scheduler,
          cache,
          documentIdentifier))
        .AddSingleton<IFileSystem, LanguageServerFilesystem>()
        .AddSingleton<IDafnyParser>(serviceProvider => {
          var options = serviceProvider.GetRequiredService<DafnyOptions>();
          return new DafnyLangParser(options,
            serviceProvider.GetRequiredService<IFileSystem>(),
            serviceProvider.GetRequiredService<TelemetryPublisherBase>(),
            serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>(),
            serviceProvider.GetRequiredService<ILogger<CachingParser>>());
        })
        .AddSingleton<ITextDocumentLoader, TextDocumentLoader>()
        .AddSingleton<INotificationPublisher, NotificationPublisher>()
        .AddSingleton<CreateMigrator>(provider => (changes, cancellationToken) => new Migrator(
          provider.GetRequiredService<ILogger<Migrator>>(),
          provider.GetRequiredService<ILogger<LegacySignatureAndCompletionTable>>(),
          changes, cancellationToken))
        .AddSingleton<ISymbolGuesser, SymbolGuesser>()
        .AddSingleton<TelemetryPublisherBase, LspTelemetryPublisher>();
    }
  }
}
