using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using DafnyCore.Generic;
using Microsoft.Dafny;
using Tomlyn;

namespace DafnyCore.Options;

// Model class for the .dtr file format for Dafny Translation Records.
// Contains the validation logic for safely consuming pre-translated libraries as well.
// See https://dafny.org/dafny/DafnyRef/DafnyRef#sec-dtr-files.
public class TranslationRecord {

  public const string CurrentFileFormatVersion = "1.0";
  public string FileFormatVersion { get; set; }

  public string DafnyVersion { get; set; }

  public Dictionary<string, Dictionary<string, object>> OptionsByModule { get; set; }

  public TranslationRecord(Program program) {
    FileFormatVersion = CurrentFileFormatVersion;
    DafnyVersion = program.Options.VersionNumber;

    OptionsByModule = new();

    foreach (var module in program.CompileModules) {
      if (module is DefaultModuleDefinition || !module.ShouldCompile(program.Compilation)) {
        continue;
      }

      // This is primarily here to exclude prefix modules
      // (e.g. something like A.B that only appears in a module A.B.C { ... } declaration)
      // since those can appear in multiple separately-compiled projects. 
      if (ModuleEmptyForCompilation(module)) {
        continue;
      }

      Dictionary<string, object> recordedOptions = new();
      OptionsByModule[module.FullDafnyName] = recordedOptions;

      foreach (var option in OptionRegistry.TranslationOptions) {
        var optionValue = program.Options.Get((dynamic)option);
        recordedOptions.Add(option.Name, optionValue);
      }
    }
  }

  public static bool ModuleEmptyForCompilation(ModuleDefinition module) {
    return !(module.DefaultClass?.Members.Any() ?? false)   // DefaultClass is null for _System
           && module.TopLevelDecls.All(d => d is DefaultClassDecl or ModuleDecl);
  }

  public static TranslationRecord Empty(Program program) {
    return new TranslationRecord() {
      FileFormatVersion = CurrentFileFormatVersion,
      DafnyVersion = program.Options.VersionNumber,
      OptionsByModule = new()
    };
  }

  public TranslationRecord() {
    // Only for TOML deserialization!
  }

  public static void ReadValidateAndMerge(Program program, string filePath, IOrigin origin) {
    var pathForErrors = program.Options.GetPrintPath(filePath);
    try {
      using TextReader reader = new StreamReader(filePath);
      var record = Read(reader);
      if (record.Validate(program, pathForErrors, origin)) {
        program.Compilation.AlreadyTranslatedRecord.Merge(program.Reporter, record, pathForErrors, origin);
      }
    } catch (FileNotFoundException) {
      program.Reporter.Error(MessageSource.Project, origin, $"file {pathForErrors} not found");
    } catch (TomlException) {
      program.Reporter.Error(MessageSource.Project, origin, $"malformed dtr file {pathForErrors}");
    }
  }

  private static TranslationRecord Read(TextReader reader) {
    return Toml.ToModel<TranslationRecord>(reader.ReadToEnd(), null, new TomlModelOptions());
  }

  public void Write(TextWriter writer) {
    writer.Write(Toml.FromModel(this, new TomlModelOptions()).Replace("\r\n", "\n"));
  }

  public void Write(ConcreteSyntaxTree writer) {
    using var textWriter = new StringWriter();
    Write(textWriter);
    writer.Write(textWriter.ToString());
  }

  private bool Validate(Program dafnyProgram, string filePath, IOrigin origin) {
    var messagePrefix = $"cannot load {filePath}";
    if (!dafnyProgram.Options.UsingNewCli) {
      dafnyProgram.Reporter.Error(MessageSource.Project, origin,
        $"{messagePrefix}: .dtr files cannot be used with the legacy CLI");
      return false;
    }

    if (dafnyProgram.Options.VersionNumber != DafnyVersion) {
      dafnyProgram.Reporter.Error(MessageSource.Project, origin,
        $"{messagePrefix}: it was built with Dafny {DafnyVersion}, which cannot be used by Dafny {dafnyProgram.Options.VersionNumber}");
      return false;
    }

    // Modules should be either previously compiled or to be compiled now, not both
    foreach (var module in dafnyProgram.CompileModules) {
      if (module.ShouldCompile(dafnyProgram.Compilation) && OptionsByModule.ContainsKey(module.FullDafnyName)) {
        dafnyProgram.Reporter.Error(MessageSource.Project, origin,
          $"{messagePrefix}: it contains translation metadata for the module {module.FullDafnyName}, which is in scope for translation in the current program");
      }
    }

    return true;
  }

  public object Get(ErrorReporter reporter, string moduleName, Option option) {
    if (OptionsByModule.TryGetValue(moduleName, out var moduleOptions)) {
      if (moduleOptions.TryGetValue(option.Name, out var manifestValue)) {
        if (TomlUtil.TryGetValueFromToml(reporter, Token.NoToken, null,
              option.Name, option.ValueType, manifestValue, out var libraryValue)) {
          return libraryValue;
        }
      }
    }

    return null;
  }

  private void Merge(ErrorReporter reporter, TranslationRecord other, string filePath, IOrigin origin) {
    // Assume both this and other have been Validate()-d already.

    var duplicateModules = OptionsByModule
      .Union(other.OptionsByModule)
      .GroupBy(p => p.Key)
      .Where(g => g.Count() > 1)
      .Select(g => g.Key)
      .ToList();
    if (duplicateModules.Any()) {
      var messagePrefix = $"cannot load {filePath}";
      foreach (var duplicateModule in duplicateModules) {
        reporter.Error(MessageSource.Project, origin,
          $"{messagePrefix}: module {duplicateModule} already appears in another translation record");
      }
      return;
    }

    OptionsByModule = OptionsByModule.Union(other.OptionsByModule).ToDictionary(p => p.Key, p => p.Value);
  }
}