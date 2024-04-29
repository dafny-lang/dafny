using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using DafnyCore.Generic;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using Tomlyn;

namespace DafnyCore.Options;

public class TranslationRecord {

  public const string CurrentFileFormatVersion = "1.0";
  public string FileFormatVersion { get; set; }

  public string DafnyVersion { get; set; }

  public Dictionary<string, Dictionary<string, object>> OptionsByModule { get; set; }


  public TranslationRecord(Program program) {
    FileFormatVersion = CurrentFileFormatVersion;
    DafnyVersion = program.Options.VersionNumber;

    OptionsByModule = new();

    foreach (var module in program.RawModules()) {
      if (module is DefaultModuleDefinition || !module.ShouldCompile(program.Compilation)) {
        continue;
      }

      Dictionary<string, object> recordedOptions = new();
      OptionsByModule[module.FullDafnyName] = recordedOptions;

      foreach (var (option, _) in OptionChecks) {
        var optionValue = program.Options.Get((dynamic)option);
        recordedOptions.Add(option.Name, optionValue);
      }
    }
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

  public static void ReadValidateAndMerge(Program program, string filePath, IToken origin) {
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
  
  private bool Validate(Program dafnyProgram, string filePath, IToken origin) {
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

    var success = true;
    // Yo dawg, we heard you liked options so we put Options in your Options... :)
    var relevantOptions = dafnyProgram.Options.Options.OptionArguments.Keys.ToHashSet();
    foreach (var (option, check) in OptionChecks) {
      // It's important to only look at the options the current command uses,
      // because other options won't be initialized to the correct default value.
      // See CommandRegistry.Create().
      if (!relevantOptions.Contains(option)) {
        continue;
      }

      var localValue = dafnyProgram.Options.Get(option);

      foreach (var moduleName in OptionsByModule.Keys) {
        var libraryValue = Get(dafnyProgram.Reporter, moduleName, option);
        success = success && check(dafnyProgram.Reporter, origin, messagePrefix, option, localValue, libraryValue);
      }
    }

    return success;
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

  private void Merge(ErrorReporter reporter, TranslationRecord other, string filePath, IToken origin) {
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

  private static readonly Dictionary<Option, OptionCompatibility.OptionCheck> OptionChecks = new();

  public static void RegisterLibraryChecks(IDictionary<Option, OptionCompatibility.OptionCheck> checks) {
    foreach (var (option, check) in checks) {
      OptionChecks.Add(option, check);
    }
  }
}