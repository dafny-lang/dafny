#nullable enable

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
using System.Threading.Tasks;
using DafnyAssembly;
using DafnyCore;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public class DafnyFile {
  public const string DafnyFileExtension = ".dfy";
  public const string DafnyBinaryExtension = ".dbin";
  public string FilePath => CanonicalPath;
  public string Extension { get; private set; }
  public string CanonicalPath { get; }
  public string BaseName { get; private set; }
  public bool ShouldNotVerify { get; private set; }
  public bool ShouldNotCompile { get; private set; }
  public DafnyOptions FileOptions { get; private set; }
  public Func<FileSnapshot> GetContent { get; set; }
  public Uri Uri { get; private set; }
  public IOrigin? Origin { get; }

  private static readonly Dictionary<Uri, Uri> ExternallyVisibleEmbeddedFiles = new();

  static DafnyFile() {
    OptionRegistry.RegisterGlobalOption(DoNotVerifyDependencies, OptionCompatibility.OptionLibraryImpliesLocalError);
  }

  public static Uri ExposeInternalUri(string externalName, Uri internalUri) {
    var externalUri = new Uri("dafny:" + externalName);
    ExternallyVisibleEmbeddedFiles[externalUri] = internalUri;
    return externalUri;
  }

  public delegate IAsyncEnumerable<DafnyFile> HandleExtension(DafnyOptions options, IFileSystem
    fileSystem, ErrorReporter reporter, Uri uri, IOrigin origin, bool asLibrary);

  private static readonly Dictionary<string, HandleExtension> ExtensionHandlers = new();

  public static void RegisterExtensionHandler(string extension, HandleExtension handler) {
    ExtensionHandlers[extension] = handler;
  }

  public static async IAsyncEnumerable<DafnyFile> CreateAndValidate(IFileSystem fileSystem,
    ErrorReporter reporter,
    DafnyOptions options, Uri uri, IOrigin? uriOrigin,
    bool asLibrary = false, string? errorOnNotRecognized = null) {

    var embeddedFile = ExternallyVisibleEmbeddedFiles.GetValueOrDefault(uri);
    if (embeddedFile != null) {
      var embeddedResults = CreateAndValidate(fileSystem, reporter, options, embeddedFile, uriOrigin, asLibrary, errorOnNotRecognized);
      await foreach (var result in embeddedResults) {
        result.Uri = uri;
        yield return result;
      }
      yield break;
    }

    uriOrigin ??= Token.NoToken;

    string extension;
    if (uri.IsFile) {
      extension = Path.GetExtension(uri.LocalPath).ToLower();
    } else if (uri.Scheme == "dllresource") {
      extension = Path.GetExtension(uri.LocalPath).ToLower();
    } else {
      extension = DafnyFileExtension;
    }

    if (uri.Scheme == "untitled" || extension == DafnyFileExtension || extension == ".dfyi" || extension == DafnyBinaryExtension) {
      var file = HandleDafnyFile(fileSystem, reporter, options, uri, uriOrigin, asLibrary);
      if (file != null) {
        yield return file;
      }
      yield break;
    }

    if (extension == DooFile.Extension) {
      await foreach (var dooResult in HandleDooFile(fileSystem, reporter, options, uri, uriOrigin, asLibrary)) {
        yield return dooResult;
      }
      yield break;
    }

    if (extension == ".dll") {
      var dllResult = HandleDll(options, uri, uriOrigin);
      if (dllResult != null) {
        yield return dllResult;
      }
      yield break;
    }

    var handler = ExtensionHandlers.GetValueOrDefault(extension);
    if (handler != null) {
      await foreach (var result in handler(options, fileSystem, reporter, uri, uriOrigin, asLibrary)) {
        yield return result;
      }
      yield break;
    }
    if (errorOnNotRecognized != null) {
      reporter.Error(MessageSource.Project, Token.Cli, errorOnNotRecognized);
    }
  }

  public static readonly Option<bool> DoNotVerifyDependencies = new("--dont-verify-dependencies",
    "Allows Dafny to accept dependencies that may not have been previously verified, which can be useful during development.");

  public static readonly Uri StdInUri = new Uri("stdin:///");

  public static DafnyFile? HandleDafnyFile(IFileSystem fileSystem,
    ErrorReporter reporter,
    DafnyOptions options,
    Uri uri, IOrigin origin, bool asLibrary = false, bool warnLibrary = true) {
    if (uri == StdInUri) {
      return HandleStandardInput(options, origin);
    }

    string canonicalPath;
    string baseName;
    if (uri.IsFile) {
      baseName = Path.GetFileName(uri.LocalPath);
      // Normalizing symbolic links appears to be not
      // supported in .Net APIs, because it is very difficult in general
      // So we will just use the absolute path, lowercased for all file systems.
      // cf. IncludeComparer.CompareTo
      canonicalPath = Canonicalize(uri.LocalPath).LocalPath;
    } else {
      canonicalPath = "";
      baseName = "";
    }

    var filePath = uri.LocalPath;
    if (!fileSystem.Exists(uri)) {
      if (0 < options.VerifySnapshots) {
        // For snapshots, we first create broken DafnyFile without content,
        // then look for the real files and create DafnuFiles for them.
        return new DafnyFile(DafnyFileExtension, canonicalPath, baseName, null!, uri, origin, null!);
      }

      reporter.Error(MessageSource.Project, origin, $"file {options.GetPrintPath(filePath)} not found");
      return null;
    }

    if (!options.Get(DoNotVerifyDependencies) && asLibrary && warnLibrary) {
      reporter.Warning(MessageSource.Project, "UnverifiedLibrary", origin,
        "The file '{0}' was passed to --library. Verification for that file might have used options incompatible with the current ones, or might have been skipped entirely. Use a .doo file to enable Dafny to check that compatible options were used",
        options.GetPrintPath(filePath));
    }

    return new DafnyFile(DafnyFileExtension, canonicalPath, baseName, () => fileSystem.ReadFile(uri), uri, origin, options) {
      ShouldNotCompile = asLibrary,
      ShouldNotVerify = asLibrary,
    };
  }

  public static DafnyFile HandleStandardInput(DafnyOptions options, IOrigin origin) {
    return new DafnyFile(DafnyFileExtension, "<stdin>", "<stdin>",
      () => new FileSnapshot(options.Input, null), StdInUri, origin, options) {
      ShouldNotCompile = false,
      ShouldNotVerify = false,
    };
  }

  /// <summary>
  /// Technically only for C#, this is for backwards compatability
  /// </summary>
  private static DafnyFile? HandleDll(DafnyOptions parseOptions, Uri uri, IOrigin origin) {

    string baseName;
    string canonicalPath;
    if (uri.IsFile) {
      baseName = Path.GetFileName(uri.LocalPath);
      // Normalizing symbolic links appears to be not
      // supported in .Net APIs, because it is very difficult in general
      // So we will just use the absolute path, lowercased for all file systems.
      // cf. IncludeComparer.CompareTo
      canonicalPath = Canonicalize(uri.LocalPath).LocalPath;
    } else {
      canonicalPath = "";
      baseName = "";
    }

    var filePath = uri.LocalPath;
    var sourceText = GetDafnySourceAttributeText(filePath);
    if (sourceText == null) {
      return null;
    }

    return new DafnyFile(".dll", canonicalPath, baseName,
      () => new FileSnapshot(new StringReader(sourceText), null), uri, origin, parseOptions) {
      ShouldNotCompile = true,
      ShouldNotVerify = true,
    };
  }

  public delegate Task<int> Executor(TextWriter outputWriter, TextWriter errorWriter, string[] arguments);

  public static async IAsyncEnumerable<DafnyFile> HandleDooFile(IFileSystem fileSystem,
    ErrorReporter reporter,
    DafnyOptions options,
    Uri uri, IOrigin origin, bool asLibrary) {
    DooFile dooFile;
    var filePath = uri.LocalPath;

    if (uri.Scheme == "dllresource") {
      var assembly = Assembly.Load(uri.Host);
      // Skip the leading "/"
      var resourceName = uri.LocalPath[1..];
      await using var stream = assembly.GetManifestResourceStream(resourceName);
      if (stream is null) {
        throw new Exception($"Cannot find embedded resource: {resourceName}");
      }

      dooFile = await DooFile.Read(stream);
    } else {
      if (!fileSystem.Exists(uri)) {
        reporter.Error(MessageSource.Project, origin, $"file {options.GetPrintPath(filePath)} not found");
        yield break;
      }

      try {
        dooFile = await DooFile.Read(filePath);
      } catch (InvalidDataException) {
        reporter.Error(MessageSource.Project, origin, $"malformed doo file {options.GetPrintPath(filePath)}");
        yield break;
      } catch (ArgumentException e) {
        reporter.Error(MessageSource.Project, origin, e.Message);
        yield break;
      }
    }

    var validDooOptions = dooFile.Validate(reporter, uri, options, origin);
    if (validDooOptions == null) {
      yield break;
    }

    // For now it's simpler to let the rest of the pipeline parse the
    // program text back into the AST representation.
    // At some point we'll likely want to serialize a program
    // more efficiently inside a .doo file, at which point
    // the DooFile class should encapsulate the serialization logic better
    // and expose a Program instead of the program text.
    yield return new DafnyFile(DooFile.Extension, Canonicalize(uri.LocalPath).LocalPath, Path.GetFileName(uri.LocalPath),
      () => new FileSnapshot(new StringReader(dooFile.ProgramText), null), uri, origin, validDooOptions) {
      ShouldNotCompile = asLibrary,
      ShouldNotVerify = true,
    };
  }

  protected DafnyFile(string extension, string canonicalPath, string baseName,
    Func<FileSnapshot> getContent, Uri uri, IOrigin? origin, DafnyOptions fileOptions) {
    Extension = extension;
    CanonicalPath = canonicalPath;
    BaseName = baseName;
    GetContent = getContent;
    Uri = uri;
    Origin = origin;
    FileOptions = fileOptions;
  }

  // Returns a canonical string for the given file path, namely one which is the same
  // for all paths to a given file and different otherwise. The best we can do is to
  // make the path absolute -- detecting case and canonicalizing symbolic and hard
  // links are difficult across file systems (which may mount parts of other filesystems,
  // with different characteristics) and is not supported by .Net libraries
  public static Uri Canonicalize(string? filePath) {
    if (filePath == null || !filePath.StartsWith("file:")) {
      return new Uri(Path.GetFullPath(filePath!));
    }

    if (Uri.IsWellFormedUriString(filePath, UriKind.RelativeOrAbsolute)) {
      return new Uri(filePath);
    }

    var potentialPrefixes = new List<string>() { "file:\\", "file:/", "file:" };
    foreach (var potentialPrefix in potentialPrefixes) {
      if (filePath.StartsWith(potentialPrefix)) {
        var withoutPrefix = filePath.Substring(potentialPrefix.Length);
        var tentativeURI = "file:///" + withoutPrefix.Replace("\\", "/");
        if (Uri.IsWellFormedUriString(tentativeURI, UriKind.RelativeOrAbsolute)) {
          return new Uri(tentativeURI);
        }
        // Recovery mechanisms for the language server
        return new Uri(filePath.Substring(potentialPrefix.Length));
      }
    }
    return new Uri(filePath.Substring("file:".Length));
  }
  public static List<string> FileNames(IReadOnlyList<DafnyFile> dafnyFiles) {
    var sourceFiles = new List<string>();
    foreach (DafnyFile f in dafnyFiles) {
      sourceFiles.Add(f.FilePath);
    }
    return sourceFiles;
  }

  private static string? GetDafnySourceAttributeText(string dllPath) {
    if (!File.Exists(dllPath)) {
      return null;
    }

    try {
      var assembly = Assembly.LoadFile(dllPath);

      foreach (DafnySourceAttribute attr in assembly.GetCustomAttributes(typeof(DafnySourceAttribute), true)) {
        return attr.dafnySourceText;
      }
    } catch (Exception) {
      // ignored
    }

    return null;
  }

  public static Uri CreateCrossPlatformUri(string path) {
    // Only fixes Unix paths on Windows
    if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows) && path.StartsWith("/")) {
      return new Uri("file://" + path);
    }
    return new Uri(path);
  }
}