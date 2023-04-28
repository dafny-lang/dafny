using Microsoft.Dafny;
using Tomlyn;

namespace DafnyCore.Test;

public class DooFileTest {
  [Fact]
  public void RoundTripCurrentVersion() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var program = ParseProgram("module MyModule { function TheAnswer(): int { 42 } }", options);
    var dooFile = new DooFile(program);

    var path = Path.GetTempFileName();
    dooFile.Write(path);
    var loadedDooFile = DooFile.Read(path);

    Assert.Equal(loadedDooFile.Manifest.DooFileVersion, DooFile.ManifestData.CurrentDooFileVersion);
    Assert.Equal(loadedDooFile.Manifest.DafnyVersion, options.VersionNumber);
    Assert.Equal(loadedDooFile.Manifest.SolverIdentifier, options.SolverIdentifier);
    Assert.Equal(loadedDooFile.Manifest.SolverVersion, options.SolverVersion.ToString());
  }

  [Fact]
  public void UnknownManifestEntries() {
    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "TestFiles/DooFileTest/badManifest.toml");
    var source = File.ReadAllText(filePath);
    Assert.Throws<TomlException>(() => DooFile.ManifestData.Read(new StringReader(source)));
  }

  private static Program ParseProgram(string dafnyProgramText, DafnyOptions options) {
    var module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
    const string fullFilePath = "foo";
    Microsoft.Dafny.Type.ResetScopes();
    var builtIns = new BuiltIns(options);
    var errorReporter = new ConsoleErrorReporter(options);
    var parseResult = Parser.Parse(dafnyProgramText, fullFilePath, "foo", module, builtIns, errorReporter);
    Assert.Equal(0, parseResult);
    return new Program(fullFilePath, module, builtIns, errorReporter);
  }
}
