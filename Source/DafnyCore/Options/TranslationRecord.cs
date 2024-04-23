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
  
  public Dictionary<string, Dictionary<string, object>> OptionsByModule { get; set;  }


  public TranslationRecord(Program program) {
    FileFormatVersion = CurrentFileFormatVersion;
    DafnyVersion = program.Options.VersionNumber;

    OptionsByModule = new();
    
    foreach (var module in program.RawModules()) {
      // TODO: Don't include the default module,
      // which is the only one that can cross compilation units
      
      if (!module.ShouldCompile(program.Compilation)) {
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
  
  public TranslationRecord() {
    OptionsByModule = new();
  }
  
  public static TranslationRecord Read(TextReader reader) {
    return Toml.ToModel<TranslationRecord>(reader.ReadToEnd(), null, new TomlModelOptions());
  }
  
  public void Write(TextWriter writer) {
    writer.Write(Toml.FromModel(this, new TomlModelOptions()).Replace("\r\n", "\n"));
  }
  
  public bool Validate(ErrorReporter reporter, string filePath, DafnyOptions options, IToken origin) {
    var messagePrefix = $"cannot load {filePath}";
    if (!options.UsingNewCli) {
      reporter.Error(MessageSource.Project, origin,
        $"{messagePrefix}: .dtr files cannot be used with the legacy CLI");
      return false;
    }

    if (options.VersionNumber != DafnyVersion) {
      reporter.Error(MessageSource.Project, origin,
        $"{messagePrefix}: it was built with Dafny {DafnyVersion}, which cannot be used by Dafny {options.VersionNumber}");
      return false;
    }

    var success = true;
    var relevantOptions = options.Options.OptionArguments.Keys.ToHashSet();
    foreach (var (option, check) in OptionChecks) {
      // It's important to only look at the options the current command uses,
      // because other options won't be initialized to the correct default value.
      // See CommandRegistry.Create().
      if (!relevantOptions.Contains(option)) {
        continue;
      }

      var localValue = options.Get(option);

      foreach (var moduleName in OptionsByModule.Keys) {
        var libraryValue = Get(reporter, moduleName, option);
        success = success && check(reporter, origin, messagePrefix, option, localValue, libraryValue);
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

  public void Merge(TranslationRecord other) {
    // TODO: check versions
    
    // TODO: This will error if any modules overlap, which is what we want,
    // but we can do much better in terms of error messages.
    OptionsByModule = OptionsByModule.Union(other.OptionsByModule).ToDictionary(p => p.Key, p => p.Value);
  }
  
  private static readonly Dictionary<Option, OptionCompatibility.OptionCheck> OptionChecks = new();
  
  public static void RegisterLibraryChecks(IDictionary<Option, OptionCompatibility.OptionCheck> checks) {
    foreach (var (option, check) in checks) {
      OptionChecks.Add(option, check);
    }
  }
}