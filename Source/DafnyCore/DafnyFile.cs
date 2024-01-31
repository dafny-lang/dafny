using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using DafnyCore;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class DafnyFile {
  public string FilePath => CanonicalPath;
  public string Extension { get; private set; }
  public string CanonicalPath { get; }
  public string BaseName { get; private set; }
  public bool IsPreverified { get; set; }
  public bool IsPrecompiled { get; set; }
  public DafnyOptions ParseOptions { get; private set; }
  public Func<TextReader> GetContent { get; set; }
  public Uri Uri { get; private set; }
  [CanBeNull] public IToken Origin { get; }

  private static readonly Dictionary<Uri, Uri> ExternallyVisibleEmbeddedFiles = new();

  public static Uri ExposeInternalUri(string externalName, Uri internalUri) {
    var externalUri = new Uri("dafny:" + externalName);
    ExternallyVisibleEmbeddedFiles[externalUri] = internalUri;
    return externalUri;
  }

  public static DafnyFile CreateAndValidate(ErrorReporter reporter, IFileSystem fileSystem,
    DafnyOptions options, Uri uri, IToken origin, string errorOnNotRecognized = null) {

    var embeddedFile = ExternallyVisibleEmbeddedFiles.GetValueOrDefault(uri);
    if (embeddedFile != null) {
      var result = CreateAndValidate(reporter, fileSystem, options, embeddedFile, origin, errorOnNotRecognized);
      if (result != null) {
        result.Uri = uri;
      }
      return result;
    }

    var filePath = uri.LocalPath;

    origin ??= Token.NoToken;

    string canonicalPath;
    string baseName;
    Func<TextReader> getContent = null;
    bool isPreverified;
    bool isPrecompiled;
    var parseOptions = options;
    var extension = ".dfy";
    if (uri.IsFile) {
      extension = Path.GetExtension(uri.LocalPath).ToLower();
      baseName = Path.GetFileName(uri.LocalPath);
      // Normalizing symbolic links appears to be not
      // supported in .Net APIs, because it is very difficult in general
      // So we will just use the absolute path, lowercased for all file systems.
      // cf. IncludeComparer.CompareTo
      canonicalPath = Canonicalize(filePath).LocalPath;
    } else if (uri.Scheme == "stdin") {
      getContent = () => options.Input;
      baseName = "<stdin>";
      canonicalPath = "<stdin>";
    } else if (uri.Scheme == "dllresource") {
      extension = Path.GetExtension(uri.LocalPath).ToLower();
      baseName = uri.LocalPath;
      canonicalPath = uri.ToString();
    } else {
      canonicalPath = "";
      baseName = "";
    }

    var filePathForErrors = options.GetPrintPath(filePath);
    if (getContent != null) {
      isPreverified = false;
      isPrecompiled = false;
    } else if (uri.Scheme == "untitled" || extension == ".dfy" || extension == ".dfyi") {
      isPreverified = false;
      isPrecompiled = false;
      if (!fileSystem.Exists(uri)) {
        if (0 < options.VerifySnapshots) {
          // For snapshots, we first create broken DafnyFile without content,
          // then look for the real files and create DafnuFiles for them.
          return new DafnyFile(extension, canonicalPath, baseName, null, uri, origin);
        }

        reporter.Error(MessageSource.Project, origin, $"file {filePathForErrors} not found");
        return null;
      }

      getContent = () => fileSystem.ReadFile(uri);
    } else if (extension == ".doo") {
      isPreverified = true;
      isPrecompiled = false;

      DooFile dooFile;
      if (uri.Scheme == "dllresource") {
        var assembly = Assembly.Load(uri.Host);
        // Skip the leading "/"
        var resourceName = uri.LocalPath[1..];
        using var stream = assembly.GetManifestResourceStream(resourceName);
        if (stream is null) {
          throw new Exception($"Cannot find embedded resource: {resourceName}");
        }

        dooFile = DooFile.Read(stream);
      } else {
        if (!fileSystem.Exists(uri)) {
          reporter.Error(MessageSource.Project, origin, $"file {filePathForErrors} not found");
          return null;
        }

        try {
          dooFile = DooFile.Read(filePath);
        } catch (InvalidDataException) {
          reporter.Error(MessageSource.Project, origin, $"malformed doo file {options.GetPrintPath(filePath)}");
          return null;
        } catch (ArgumentException e) {
          reporter.Error(MessageSource.Project, origin, e.Message);
          return null;
        }

      }

      var validDooOptions = dooFile.Validate(reporter, filePathForErrors, options, origin);
      if (validDooOptions == null) {
        return null;
      }

      parseOptions = validDooOptions;

      // For now it's simpler to let the rest of the pipeline parse the
      // program text back into the AST representation.
      // At some point we'll likely want to serialize a program
      // more efficiently inside a .doo file, at which point
      // the DooFile class should encapsulate the serialization logic better
      // and expose a Program instead of the program text.
      getContent = () => new StringReader(dooFile.ProgramText);
    } else if (extension == ".dll") {
      isPreverified = true;
      // Technically only for C#, this is for backwards compatability
      isPrecompiled = true;

      var sourceText = GetDafnySourceAttributeText(filePath);
      if (sourceText == null) {
        return null;
      }
      getContent = () => new StringReader(sourceText);
    } else {
      if (errorOnNotRecognized != null) {
        reporter.Error(MessageSource.Project, Token.Cli, errorOnNotRecognized);
      }
      return null;
    }

    return new DafnyFile(extension, canonicalPath, baseName, getContent, uri, origin) {
      IsPrecompiled = isPrecompiled,
      IsPreverified = isPreverified,
      ParseOptions = parseOptions,
    };
  }

  protected DafnyFile(string extension, string canonicalPath, string baseName,
    Func<TextReader> getContent, Uri uri, [CanBeNull] IToken origin) {
    Extension = extension;
    CanonicalPath = canonicalPath;
    BaseName = baseName;
    GetContent = getContent;
    Uri = uri;
    Origin = origin;
  }

  // Returns a canonical string for the given file path, namely one which is the same
  // for all paths to a given file and different otherwise. The best we can do is to
  // make the path absolute -- detecting case and canonicalizing symbolic and hard
  // links are difficult across file systems (which may mount parts of other filesystems,
  // with different characteristics) and is not supported by .Net libraries
  public static Uri Canonicalize(string filePath) {
    if (filePath == null || !filePath.StartsWith("file:")) {
      return new Uri(Path.GetFullPath(filePath));
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

  private static string GetDafnySourceAttributeText(string dllPath) {
    if (!File.Exists(dllPath)) {
      return null;
    }
    using var dllFs = new FileStream(dllPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
    using var dllPeReader = new PEReader(dllFs);
    var dllMetadataReader = dllPeReader.GetMetadataReader();

    foreach (var attrHandle in dllMetadataReader.CustomAttributes) {
      var attr = dllMetadataReader.GetCustomAttribute(attrHandle);
      try {
        /* The cast from EntityHandle to MemberReferenceHandle is overriden, uses private members, and throws
         * an InvalidCastException if it fails. We have no other option than to use it and catch the exception.
         */
        var constructor = dllMetadataReader.GetMemberReference((MemberReferenceHandle)attr.Constructor);
        var attrType = dllMetadataReader.GetTypeReference((TypeReferenceHandle)constructor.Parent);
        if (dllMetadataReader.GetString(attrType.Name) == "DafnySourceAttribute") {
          var decoded = attr.DecodeValue(new StringOnlyCustomAttributeTypeProvider());
          return (string)decoded.FixedArguments[0].Value;
        }
      } catch (InvalidCastException) {
        // Ignore - the Handle casts are handled as custom explicit operators,
        // and there's no way I can see to test if the cases will succeed ahead of time.
      }
    }

    return null;
  }

  // Dummy implementation of ICustomAttributeTypeProvider, providing just enough
  // functionality to successfully decode a DafnySourceAttribute value.
  private class StringOnlyCustomAttributeTypeProvider : ICustomAttributeTypeProvider<System.Type> {
    public System.Type GetPrimitiveType(PrimitiveTypeCode typeCode) {
      if (typeCode == PrimitiveTypeCode.String) {
        return typeof(string);
      }
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) {
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind) {
      throw new NotImplementedException();
    }

    public System.Type GetSZArrayType(System.Type elementType) {
      throw new NotImplementedException();
    }

    public System.Type GetSystemType() {
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromSerializedName(string name) {
      throw new NotImplementedException();
    }

    public PrimitiveTypeCode GetUnderlyingEnumType(System.Type type) {
      throw new NotImplementedException();
    }

    public bool IsSystemType(System.Type type) {
      throw new NotImplementedException();
    }
  }
}