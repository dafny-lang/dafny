using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class CppBackend : ExecutableBackend {

  // Opt-in arbitrary-precision support. `--bignum=<impl>` picks the big-integer library
  // behind the runtime header's seam, enabling Dafny's unbounded `int`, exact `real` and
  // `multiset`. Without the flag the C++ backend rejects those features as before and needs
  // no library. Only `boost` is implemented today; the flag is an enum so further backends
  // (a verified Dafny bignum, std::big_int, ...) can be added as additional values, each
  // selecting a different typedef in the runtime seam.
  public const string BignumBoost = "boost";
  public static readonly Option<string> BignumOption = new("--bignum",
    @"Enable Dafny's unbounded int, exact real and multiset in the C++ backend, using the given big-integer library. Currently only 'boost' (Boost.Multiprecision, header-only; provide Boost via -I or DAFNY_CPP_BOOST_PREFIX).") {
  };

  static CppBackend() {
    BignumOption.FromAmong(BignumBoost);
    OptionRegistry.RegisterOption(BignumOption, OptionScope.Translation);
  }

  public override IEnumerable<Option> SupportedOptions => new List<Option> { BignumOption };

  // The selected bignum implementation, or null when the flag is absent.
  private string Bignum => Options.Get(BignumOption);

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new CppCodeGenerator(Options, Reporter, OtherFileNames);
  }

  private string ComputeExeName(string targetFilename) {
    return Path.ChangeExtension(Path.GetFullPath(targetFilename), "exe");
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    var assemblyLocation = System.Reflection.Assembly.GetExecutingAssembly().Location;
    Contract.Assert(assemblyLocation != null);
    var codebase = Path.GetDirectoryName(assemblyLocation);
    Contract.Assert(codebase != null);
    var gxxArgs = new List<string> {
      "-Wall",
      "-Wextra",
      "-Wpedantic",
      "-Wno-unused-variable",
      "-Wno-deprecated-copy",
      "-Wno-unused-label",
      "-Wno-unused-but-set-variable",
      "-Wno-unknown-warning-option",
      "-g",
      "-std=c++17",
      "-I", codebase,
    };
    // -DDAFNY_BIGNUM turns on the runtime header's bignum block; -DDAFNY_BIGNUM_<impl>
    // selects the typedef/helpers for the chosen library. Each case adds whatever that
    // library needs on the g++ line (include path, link flags). Adding a backend = a new
    // case here plus a new #if branch in the runtime seam.
    switch (Bignum) {
      case BignumBoost:
        // Boost.Multiprecision cpp_int is header-only, so it only needs an include path
        // and nothing to link. Honour DAFNY_CPP_BOOST_PREFIX if set, else fall back to the
        // common macOS Homebrew prefix (harmless if absent; on Linux the headers are
        // normally already on the default search path).
        var boostPrefix = Environment.GetEnvironmentVariable("DAFNY_CPP_BOOST_PREFIX");
        if (string.IsNullOrEmpty(boostPrefix) && Directory.Exists("/opt/homebrew")) {
          boostPrefix = "/opt/homebrew";
        }
        if (!string.IsNullOrEmpty(boostPrefix)) {
          gxxArgs.Add($"-I{boostPrefix}/include");
        }
        gxxArgs.Add("-DDAFNY_BIGNUM");
        gxxArgs.Add("-DDAFNY_BIGNUM_BOOST");
        break;
    }
    gxxArgs.Add("-o");
    gxxArgs.Add(ComputeExeName(targetFilename));
    gxxArgs.Add(targetFilename);
    var psi = PrepareProcessStartInfo("g++", gxxArgs);
    await using var statusWriter = outputWriter.StatusWriter();
    return (0 == await RunProcess(psi, statusWriter, statusWriter, "Error while compiling C++ files."), null);
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, IDafnyOutputWriter outputWriter) {
    var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return 0 == await RunProcess(psi, sw, ew);
  }

  public override Command GetCommand() {
    var cmd = base.GetCommand();
    cmd.Description = $@"Translate Dafny sources to {TargetName} source and build files.

This back-end has various limitations (see Docs/Compilation/Cpp.md).
This includes lack of support for most higher order functions,
and advanced features like traits or co-inductive types.
Pass --bignum=boost to enable unbounded integers (int), exact reals (real) and
multisets via Boost.Multiprecision (header-only; provide Boost via -I or
DAFNY_CPP_BOOST_PREFIX).";
    return cmd;
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".h" };

  public override string TargetName => "C++";
  public override bool IsStable => true;
  public override string TargetExtension => "cpp";

  public override bool SupportsInMemoryCompilation => false;

  public override bool TextualTargetIsExecutable => false;

  public CppBackend(DafnyOptions options) : base(options) {
  }
}
