using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text;

namespace Microsoft.Dafny;

public record DfyParseResult(int ErrorCount, FileModuleDefinition Module);

public class ParseUtils {
  
  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members) from "filename"
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  public static DfyParseResult Parse(TextReader reader, Uri /*!*/ uri, BuiltIns builtIns,
      Errors /*!*/ errors) /* throws System.IO.IOException */ {
    Contract.Requires(uri != null);
    var text = SourcePreprocessor.ProcessDirectives(reader, new List<string>());
    return Parse(text, uri, builtIns, errors);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  public static DfyParseResult Parse(string /*!*/ s, Uri /*!*/ uri, BuiltIns builtIns, ErrorReporter reporter) {
    Contract.Requires(s != null);
    Contract.Requires(uri != null);
    Errors errors = new Errors(reporter);
    return Parse(s, uri, builtIns, errors);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner with the given Errors sink.
  ///</summary>
  public static DfyParseResult Parse(string /*!*/ s, Uri /*!*/ uri, 
    BuiltIns builtIns, Errors /*!*/ errors) {
    Parser parser = SetupParser(s, uri, builtIns, errors);
    parser.Parse();
    
    if (parser.theModule.DefaultClass.Members.Count == 0 && parser.theModule.Includes.Count == 0 && parser.theModule.TopLevelDecls.Count == 1
        && (parser.theModule.PrefixNamedModules == null || parser.theModule.PrefixNamedModules.Count == 0)) {
      errors.Warning(new Token(1, 1) { Uri = uri }, "File contains no code");
    }
    
    return new DfyParseResult(parser.errors.ErrorCount, parser.theModule);
  }

  public static Parser SetupParser(string /*!*/ s, Uri /*!*/ uri, 
    BuiltIns builtIns, Errors /*!*/ errors) {
    Contract.Requires(s != null);
    Contract.Requires(uri != null);
    Contract.Requires(errors != null);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ParseErrors).TypeHandle);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ResolutionErrors).TypeHandle);
    byte[] /*!*/
      buffer = cce.NonNull(UTF8Encoding.Default.GetBytes(s));
    MemoryStream ms = new MemoryStream(buffer, false);
    var firstToken = new Token {
      Uri = uri
    };
    
    // if ((module.RootToken.Filepath ?? "") == "") {
    //   // This is the first module
    //   module.RootToken.Uri = uri;
    //   firstToken = module.RootToken;
    // } else {
    //   firstToken = new Token(); // It's an included file
    // }

    Scanner scanner = new Scanner(ms, errors, uri, firstToken: firstToken);
    return new Parser(scanner, errors, builtIns);
  }

  public static int Parse(string source, Uri uri, LiteralModuleDecl builtIns, BuiltIns reporter, ErrorReporter errorReporter) {
    throw new NotImplementedException();
  }
}