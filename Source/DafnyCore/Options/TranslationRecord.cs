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
      if (!module.ShouldCompile(program.Compilation)) {
        continue;
      }
      
      Dictionary<string, object> recordedOptions = new();
      OptionsByModule[module.FullDafnyName] = recordedOptions;
      
      // TODO: Just recording one option for a POC first
      recordedOptions["outer-module"] = program.Options.Get(IExecutableBackend.OuterModule);
    }
  }
  
  public TranslationRecord() {
    OptionsByModule = new();
  }
  
  public static TranslationRecord Read(TextReader reader) {
    return Toml.ToModel<TranslationRecord>(reader.ReadToEnd(), null, new TomlModelOptions());
  }
  
  public void Write(ConcreteSyntaxTree writer) {
    writer.Write(Toml.FromModel(this, new TomlModelOptions()).Replace("\r\n", "\n"));
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
}