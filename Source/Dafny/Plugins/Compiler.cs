// SPDX-License-Identifier: MIT
#nullable enable

using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Reflection;

namespace Microsoft.Dafny.Plugins;

/// <summary>
/// A class that plugins should extend in order to provide an extra Compiler to the pipeline.
///
/// If the plugin defines no PluginConfiguration, then Dafny will instantiate every sub-class
/// of Compiler from the plugin.
/// </summary>
public abstract class Compiler {
  public abstract IReadOnlySet<string> SupportedExtensions { get; }

  public abstract string TargetLanguage { get; }
  public abstract string TargetExtension { get; }
  public virtual string TargetId => TargetExtension;

  public virtual string Basename(string dafnyProgramName) =>
    Path.GetFileNameWithoutExtension(dafnyProgramName);
  public virtual string TargetBaseDir(string baseName) =>
    "";

  public abstract string PublicIdProtect(string name);
  public virtual string GetCompileName(bool isDefaultModule, string moduleName, string compileName) =>
    PublicIdProtect(moduleName) + "." + PublicIdProtect(compileName);

  public virtual IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "ulong", "long" };

  public abstract bool TextualTargetIsExecutable { get; }
  public abstract bool SupportsInMemoryCompilation { get; }

  protected ErrorReporter? Reporter = null;
  protected ReadOnlyCollection<string>? OtherFileNames = null;

  // This method exists because compilers are constructed very early in the pipeline (to consult their
  // `SupportedExtensions`, `TargetLanguage`, etc.).  C# doesn't support static fields in abstract classes, so we have
  // to create an instance to access these parameters.  The alternative is to have a factory class, but we deemed the
  // added complexity unnecessary.
  public virtual void LateInitialize(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    Reporter = reporter;
    OtherFileNames = otherFileNames;
  }


  /// <summary>
  /// Remove previously generated source files.  This is only applicable to compilers that put sources in a separate
  /// directory (e.g. Java).  For other compilers, this method should do nothing.
  /// </summary>
  /// <param name="sourceDirectory">Name of the directory to delete.</param>
  public virtual void CleanSourceDirectory(string sourceDirectory) { }

  public abstract void Compile(Program dafnyProgram, ConcreteSyntaxTree output);

  /// <summary>
  /// Emits a call to "mainMethod" as the program's entry point, if such an explicit call is
  /// required in the target language.
  /// </summary>
  public abstract void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree);

  /// <summary>
  /// Compile the target program known as "dafnyProgramName".
  /// "targetProgramText" contains the program text.
  /// If "targetFilename" is non-null, it is the name of the target program text stored as a
  /// file. "targetFileName" must be non-null if "otherFileNames" is nonempty.
  /// "otherFileNames" is a list of other files to include in the compilation.
  ///
  /// When "callToMain" is non-null, the program contains a "Main()" program.
  ///
  /// Upon successful compilation, "runAfterCompile" says whether or not to execute the program.
  ///
  /// Output any errors to "outputWriter".
  /// Returns "false" if there were errors. Then, "compilationResult" should not be used.
  /// Returns "true" on success. Then, "compilationResult" is a value that can be passed in to
  /// the instance's "RunTargetProgram" method.
  /// </summary>
  public abstract bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string pathsFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter, out object compilationResult);

  /// <summary>
  /// Runs a target program after it has been successfully compiled.
  /// dafnyProgram, targetProgramText, targetFilename, and otherFileNames are the same as the corresponding parameters to "CompileTargetProgram".
  /// "callToMain" is an explicit call to Main, as required by the target compilation language.
  /// "compilationResult" is a value returned by "CompileTargetProgram" for these parameters.
  ///
  /// Returns "true" on success, "false" on error. Any errors are output to "outputWriter".
  /// </summary>
  public abstract bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string pathsFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter);

  public abstract void WriteCoverageLegendFile();
}
