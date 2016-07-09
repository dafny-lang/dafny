using System.Collections.Generic;
using System.Numerics;
using Microsoft.Boogie;
using System.IO;
using System.Text;


using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {



public class Parser {
	public const int _EOF = 0;
	public const int _ident = 1;
	public const int _digits = 2;
	public const int _hexdigits = 3;
	public const int _decimaldigits = 4;
	public const int _arrayToken = 5;
	public const int _bool = 6;
	public const int _char = 7;
	public const int _int = 8;
	public const int _nat = 9;
	public const int _real = 10;
	public const int _object = 11;
	public const int _string = 12;
	public const int _set = 13;
	public const int _iset = 14;
	public const int _multiset = 15;
	public const int _seq = 16;
	public const int _map = 17;
	public const int _imap = 18;
	public const int _charToken = 19;
	public const int _stringToken = 20;
	public const int _colon = 21;
	public const int _comma = 22;
	public const int _verticalbar = 23;
	public const int _doublecolon = 24;
	public const int _boredSmiley = 25;
	public const int _bullet = 26;
	public const int _dot = 27;
	public const int _semi = 28;
	public const int _darrow = 29;
	public const int _arrow = 30;
	public const int _assume = 31;
	public const int _calc = 32;
	public const int _case = 33;
	public const int _then = 34;
	public const int _else = 35;
	public const int _decreases = 36;
	public const int _invariant = 37;
	public const int _function = 38;
	public const int _predicate = 39;
	public const int _inductive = 40;
	public const int _lemma = 41;
	public const int _copredicate = 42;
	public const int _modifies = 43;
	public const int _reads = 44;
	public const int _requires = 45;
	public const int _lbrace = 46;
	public const int _rbrace = 47;
	public const int _lbracket = 48;
	public const int _rbracket = 49;
	public const int _openparen = 50;
	public const int _closeparen = 51;
	public const int _openAngleBracket = 52;
	public const int _closeAngleBracket = 53;
	public const int _eq = 54;
	public const int _neq = 55;
	public const int _neqAlt = 56;
	public const int _star = 57;
	public const int _notIn = 58;
	public const int _ellipsis = 59;
	public const int maxT = 142;

	const bool _T = true;
	const bool _x = false;
	const int minErrDist = 2;

	public Scanner scanner;
	public Errors  errors;

	public Token t;    // last recognized token
	public Token la;   // lookahead token
	int errDist = minErrDist;

readonly Expression/*!*/ dummyExpr;
readonly AssignmentRhs/*!*/ dummyRhs;
readonly FrameExpression/*!*/ dummyFrameExpr;  
readonly Statement/*!*/ dummyStmt;
readonly ModuleDecl theModule;
readonly BuiltIns theBuiltIns;
readonly bool theVerifyThisFile;
int anonymousIds = 0;

/// <summary>
/// Holds the modifiers given for a declaration
///
/// Not all modifiers are applicable to all kinds of declarations.
/// Errors are given when a modify does not apply.
/// We also record the tokens for the specified modifiers so that
/// they can be used in error messages.
/// </summary>
struct DeclModifierData {
  public bool IsAbstract;
  public IToken AbstractToken;
  public bool IsGhost;
  public IToken GhostToken;
  public bool IsStatic;
  public IToken StaticToken;
  public bool IsProtected;
  public IToken ProtectedToken;
  public bool IsExtern;
  public IToken ExternToken;
  public StringLiteralExpr ExternName;

}

// Check that token has not been set, then set it.
public void CheckAndSetToken(ref IToken token)
{
    if (token != null) {
      SemErr(t, "Duplicate declaration modifier: " + t.val);
    }
    token = t;
}

/// <summary>
// A flags type used to tell what declaration modifiers are allowed for a declaration.
/// </summary>
[Flags]
enum AllowedDeclModifiers {
  None = 0,
  Abstract = 1,
  Ghost = 2,

  // Means ghost not allowed because already implicitly ghost.
  AlreadyGhost = 4,
  Static = 8,
  Protected = 16, 
  Extern = 32
};

/// <summary>
/// Check the declaration modifiers against those that are allowed.
///
/// The 'allowed' parameter specifies which declaratio modifiers are allowed.
/// The 'declCaption' parameter should be a string describing the kind of declaration. 
/// It is used in error messages.
/// Any declaration modifiers that are present but not allowed are cleared.
///</summary>
void CheckDeclModifiers(DeclModifierData dmod, string declCaption, AllowedDeclModifiers allowed)
{
  if (dmod.IsAbstract && ((allowed & AllowedDeclModifiers.Abstract) == 0)) {
    SemErr(dmod.AbstractToken, declCaption + " cannot be declared 'abstract'.");
    dmod.IsAbstract = false;
  }
  if (dmod.IsGhost) {
    if ((allowed & AllowedDeclModifiers.AlreadyGhost) != 0) {
      SemErr(dmod.GhostToken, declCaption + " cannot be declared ghost (they are 'ghost' by default).");
      dmod.IsGhost = false;
    } else if ((allowed & AllowedDeclModifiers.Ghost) == 0) {
      SemErr(dmod.GhostToken, declCaption + " cannot be declared 'ghost'.");
      dmod.IsGhost = false;
    }
  }
  if (dmod.IsStatic && ((allowed & AllowedDeclModifiers.Static) == 0)) {
    SemErr(dmod.StaticToken, declCaption + " cannot be declared 'static'.");
    dmod.IsStatic = false;
  }
  if (dmod.IsProtected && ((allowed & AllowedDeclModifiers.Protected) == 0)) {
    SemErr(dmod.ProtectedToken, declCaption + " cannot be declared 'protected'.");
    dmod.IsProtected = false;
  }
  if (dmod.IsExtern && ((allowed & AllowedDeclModifiers.Extern) == 0)) {
    SemErr(dmod.ExternToken, declCaption + " cannot be declared 'extern'.");
    dmod.IsExtern = false;
  }
}

/// <summary>
/// Encode an 'extern' declaration modifier as an {:extern name} attribute.
///
/// We also include an {:axiom} attribute since the specification of an
/// external entity is assumed to hold, but only for methods or functions.
///</summary>
static void EncodeExternAsAttribute(DeclModifierData dmod, ref Attributes attrs, IToken/*!*/ id, bool needAxiom) {
  if (dmod.IsExtern) {
    StringLiteralExpr name = dmod.ExternName;
    if (name == null) {
      bool isVerbatimString = false;
      name = new StringLiteralExpr(id, id.val, isVerbatimString);
    }
    var args = new List<Expression>();
    args.Add(name);
    attrs = new Attributes("extern", args, attrs);

    // Also 'extern' implies 'axiom' for methods or functions.
    if (needAxiom) {
      attrs = new Attributes("axiom", new List<Expression>(), attrs);
    }
  }
}

///<summary>
/// Parses top-level things (modules, classes, datatypes, class members) from "filename"
/// and appends them in appropriate form to "module".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string/*!*/ filename, ModuleDecl module, BuiltIns builtIns, Errors/*!*/ errors, bool verifyThisFile=true) /* throws System.IO.IOException */ {
  Contract.Requires(filename != null);
  Contract.Requires(module != null);
  string s;
  if (filename == "stdin.dfy") {
    s = Microsoft.Boogie.ParserHelper.Fill(System.Console.In, new List<string>());
    return Parse(s, filename, filename, module, builtIns, errors, verifyThisFile);
  } else {
    using (System.IO.StreamReader reader = new System.IO.StreamReader(filename)) {
      s = Microsoft.Boogie.ParserHelper.Fill(reader, new List<string>());
      return Parse(s, filename, DafnyOptions.Clo.UseBaseNameForFileName ? Path.GetFileName(filename) : filename, module, builtIns, errors, verifyThisFile);
    }
  }
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "module".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ fullFilename, string/*!*/ filename, ModuleDecl module, BuiltIns builtIns, ErrorReporter reporter, bool verifyThisFile=true) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(module != null);
  Errors errors = new Errors(reporter);
  return Parse(s, fullFilename, filename, module, builtIns, errors, verifyThisFile);
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "module".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner with the given Errors sink.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ fullFilename, string/*!*/ filename, ModuleDecl module,
                         BuiltIns builtIns, Errors/*!*/ errors, bool verifyThisFile=true) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(module != null);
  Contract.Requires(errors != null);
  byte[]/*!*/ buffer = cce.NonNull( UTF8Encoding.Default.GetBytes(s));
  MemoryStream ms = new MemoryStream(buffer,false);
  Scanner scanner = new Scanner(ms, errors, fullFilename, filename);
  Parser parser = new Parser(scanner, errors, module, builtIns, verifyThisFile);
  parser.Parse();
  return parser.errors.ErrorCount;
}
public Parser(Scanner/*!*/ scanner, Errors/*!*/ errors, ModuleDecl module, BuiltIns builtIns, bool verifyThisFile=true)
  : this(scanner, errors)  // the real work
{
  // initialize readonly fields
  dummyExpr = new LiteralExpr(Token.NoToken);
  dummyRhs = new ExprRhs(dummyExpr, null);
  dummyFrameExpr = new FrameExpression(dummyExpr.tok, dummyExpr, null);
  dummyStmt = new ReturnStmt(Token.NoToken, Token.NoToken, null);
  theModule = module;
  theBuiltIns = builtIns;
  theVerifyThisFile = verifyThisFile;
}

bool IsAttribute() {
  Token x = scanner.Peek();
  return la.kind == _lbrace && x.kind == _colon;
}

bool IsAlternative() {
  Token x = scanner.Peek();
  return la.kind == _lbrace && x.kind == _case;
}

// an existential guard starts with an identifier and is then followed by
// * a colon (if the first identifier is given an explicit type),
// * a comma (if there's a list a bound variables and the first one is not given an explicit type),
// * a start-attribute (if there's one bound variable and it is not given an explicit type and there are attributes), or
// * a bored smiley (if there's one bound variable and it is not given an explicit type).
bool IsExistentialGuard() {
  scanner.ResetPeek();
  if (la.kind == _ident) {
    Token x = scanner.Peek();
    if (x.kind == _colon || x.kind == _comma || x.kind == _boredSmiley) {
      return true;
    } else if (x.kind == _lbrace) {
      x = scanner.Peek();
      return x.kind == _colon;
    }
  }
  return false;
}

bool IsLoopSpec() {
  return la.kind == _invariant | la.kind == _decreases | la.kind == _modifies;
}

bool IsFunctionDecl() {
  switch (la.kind) {
    case _function:
    case _predicate:
    case _copredicate:
      return true;
    case _inductive:
      return scanner.Peek().kind != _lemma;
    default:
      return false;
  }
}

bool IsParenStar() {
  scanner.ResetPeek();
  Token x = scanner.Peek();
  return la.kind == _openparen && x.kind == _star;
}

bool IsEquivOp() {
  return la.val == "<==>" || la.val == "\u21d4";
}
bool IsImpliesOp() {
  return la.val == "==>" || la.val == "\u21d2";
}
bool IsExpliesOp() {
  return la.val == "<==" || la.val == "\u21d0";
}
bool IsAndOp() {
  return la.val == "&&" || la.val == "\u2227";
}
bool IsOrOp() {
  return la.val == "||" || la.val == "\u2228";
}
bool IsRelOp() {
  return la.val == "=="
      || la.val == "<"
      || la.val == ">"
      || la.val == "<="
      || la.val == ">="
      || la.val == "!="
      || la.val == "in"
      || la.kind == _notIn
      || la.val =="!"
      || la.val == "\u2260"
      || la.val == "\u2264"
      || la.val == "\u2265";
}
bool IsAddOp() {
  return la.val == "+" || la.val == "-";
}
bool IsMulOp() {
  return la.kind == _star || la.val == "/" || la.val == "%";
}
bool IsQSep() {
  return la.kind == _doublecolon || la.kind == _bullet;
}

bool IsNonFinalColon() {
  return la.kind == _colon && scanner.Peek().kind != _rbracket;
}
bool IsMapDisplay() {
  return la.kind == _map && scanner.Peek().kind == _lbracket;
}
bool IsIMapDisplay() {
  return la.kind == _imap && scanner.Peek().kind == _lbracket;
}
bool IsISetDisplay() {
  return la.kind == _iset && scanner.Peek().kind == _lbrace;
}

bool IsSuffix() {
  return la.kind == _dot || la.kind == _lbracket || la.kind == _openparen;
}

string UnwildIdent(string x, bool allowWildcardId) {
  if (x.StartsWith("_")) {
    if (allowWildcardId && x.Length == 1) {
      return "_v" + anonymousIds++;
    } else {
      SemErr("cannot declare identifier beginning with underscore");
    }
  }
  return x;
}

bool IsLambda(bool allowLambda)
{
  if (!allowLambda) {
    return false;
  }
  scanner.ResetPeek();
  Token x;
  // peek at what might be a signature of a lambda expression
  if (la.kind == _ident) {
    // cool, that's the entire candidate signature
  } else if (la.kind != _openparen) {
    return false;  // this is not a lambda expression
  } else {
    int identCount = 0;
    x = scanner.Peek();
    while (x.kind != _closeparen) {
      if (identCount != 0) {
        if (x.kind != _comma) {
          return false;  // not the signature of a lambda
        }
        x = scanner.Peek();
      }
      if (x.kind != _ident) {
        return false;  // not a lambda expression
      }
      identCount++;
      x = scanner.Peek();
      if (x.kind == _colon) {
        // a colon belongs only in a lamdba signature, so this must be a lambda (or something ill-formed)
        return true;
      }
    }
  }
  // What we have seen so far could have been a lambda signature or could have been some
  // other expression (in particular, an identifier, a parenthesized identifier, or a
  // tuple all of whose subexpressions are identifiers).
  // It is a lambda expression if what follows is something that must be a lambda.
  x = scanner.Peek();
  return x.kind == _darrow || x.kind == _arrow || x.kind == _reads || x.kind == _requires;
}

bool IsIdentParen() {
  Token x = scanner.Peek();
  return la.kind == _ident && x.kind == _openparen;
}

bool IsIdentColonOrBar() {
  Token x = scanner.Peek();
  return la.kind == _ident && (x.kind == _colon || x.kind == _verticalbar);
}

bool SemiFollowsCall(bool allowSemi, Expression e) {
  return allowSemi && la.kind == _semi && e is ApplySuffix;
}

bool CloseOptionalBrace(bool usesOptionalBrace) {
  return usesOptionalBrace && la.kind == _rbrace;
}

bool IsNotEndOfCase() {
  return la.kind != _EOF && la.kind != _rbrace && la.kind != _case;
}

/* The following is the largest lookahead there is. It needs to check if what follows
 * can be nothing but "<" Type { "," Type } ">".
 */
bool IsGenericInstantiation() {
  scanner.ResetPeek();
  IToken pt = la;
  if (!IsTypeList(ref pt)) {
    return false;
  }
  /* There are ambiguities in the parsing.  For example:
   *     F( a < b , c > (d) )
   * can either be a unary function F whose argument is a function "a" with type arguments "<b,c>" and
   * parameter "d", or can be a binary function F with the two boolean arguments "a < b" and "c > (d)".
   * To make the situation a little better, we (somewhat heuristically) look at the character that
   * follows the ">".  Note that if we, contrary to a user's intentions, pick "a<b,c>" out as a function
   * with a type instantiation, the user can disambiguate it by making sure the ">" sits inside some
   * parentheses, like:
   *     F( a < b , (c > (d)) )
   */
  switch (pt.kind) {
    case _dot:  // here, we're sure it must have been a type instantiation we saw, because an expression cannot begin with dot
    case _openparen:  // it was probably a type instantiation of a function/method
    case _lbracket:  // it is possible that it was a type instantiation
    case _lbrace:  // it was probably a type instantiation of a function/method
    // In the following cases, we're sure we must have read a type instantiation that just ended an expression
    case _closeparen:
    case _rbracket:
    case _rbrace:
    case _semi:
    case _then:
    case _else:
    case _case:
    case _eq:
    case _neq:
    case _neqAlt:
    case _openAngleBracket:
    case _closeAngleBracket:
      return true;
    default:
      return false;
  }
}
/* Returns true if the next thing is of the form:
 *     "<" Type { "," Type } ">"
 */
bool IsTypeList(ref IToken pt) {
  if (pt.kind != _openAngleBracket) {
    return false;
  }
  pt = scanner.Peek();
  return IsTypeSequence(ref pt, _closeAngleBracket);
}
/* Returns true if the next thing is of the form:
 *     Type { "," Type }
 * followed by an endBracketKind.
 */
bool IsTypeSequence(ref IToken pt, int endBracketKind) {
  while (true) {
    if (!IsType(ref pt)) {
      return false;
    }
    if (pt.kind == endBracketKind) {
      // end of type list
      pt = scanner.Peek();
      return true;
    } else if (pt.kind == _comma) {
      // type list continues
      pt = scanner.Peek();
    } else {
      // not a type list
      return false;
    }
  }
}
bool IsType(ref IToken pt) {
  switch (pt.kind) {
    case _bool:
    case _char:
    case _nat:
    case _int:
    case _real:
    case _object:
    case _string:
      pt = scanner.Peek();
      return true;
    case _arrayToken:
    case _set:
    case _iset:
    case _multiset:
    case _seq:
    case _map:
    case _imap:
      pt = scanner.Peek();
      return pt.kind != _openAngleBracket || IsTypeList(ref pt);
    case _ident:
      while (true) {
        // invariant: next token is an ident
        pt = scanner.Peek();
        if (pt.kind == _openAngleBracket && !IsTypeList(ref pt)) {
          return false;
        }
        if (pt.kind != _dot) {
          // end of the type
          return true;
        }
        pt = scanner.Peek();  // get the _dot
        if (pt.kind != _ident) {
          return false;
        }
      }
    case _openparen:
      pt = scanner.Peek();
      if (pt.kind == _closeparen) {
        // end of type list
        pt = scanner.Peek();
        return true;
      }
      return IsTypeSequence(ref pt, _closeparen);
    default:
      return false;
  }
}


void ConvertKeywordTokenToIdent() {
  var oldKind = la.kind;
  la.kind = _ident;

  // call CheckLiteral with la
  var origT = t;
  t = la;
  scanner.CheckLiteral();
  t = origT;

  if (la.kind != _ident) {
    // it has been changed by CheckLiteral, which means it was a keyword
    la.kind = _ident;  // convert it to an ident
  } else {
    // la was something other than a keyword
    la.kind = oldKind;
  }
}


/*--------------------------------------------------------------------------*/


	public Parser(Scanner scanner, Errors errors) {
		this.scanner = scanner;
		this.errors = errors;
		Token tok = new Token();
		tok.val = "";
		this.la = tok;
		this.t = new Token(); // just to satisfy its non-null constraint
	}

	void SynErr (int n) {
		if (errDist >= minErrDist) errors.SynErr(la.filename, la.line, la.col, n);
		errDist = 0;
	}

	public void SemErr (string msg) {
		Contract.Requires(msg != null);
		if (errDist >= minErrDist) errors.SemErr(t, msg);
		errDist = 0;
	}

	public void SemErr(IToken tok, string msg) {
	  Contract.Requires(tok != null);
	  Contract.Requires(msg != null);
	  errors.SemErr(tok, msg);
	}

	void Get () {
		for (;;) {
			t = la;
			la = scanner.Scan();
			if (la.kind <= maxT) { ++errDist; break; }

			la = t;
		}
	}

	void Expect (int n) {
		if (la.kind==n) Get(); else { SynErr(n); }
	}

	bool StartOf (int s) {
		return set[s, la.kind];
	}

	void ExpectWeak (int n, int follow) {
		if (la.kind == n) Get();
		else {
			SynErr(n);
			while (!StartOf(follow)) Get();
		}
	}


	bool WeakSeparator(int n, int syFol, int repFol) {
		int kind = la.kind;
		if (kind == n) {Get(); return true;}
		else if (StartOf(repFol)) {return false;}
		else {
			SynErr(n);
			while (!(set[syFol, kind] || set[repFol, kind] || set[0, kind])) {
				Get();
				kind = la.kind;
			}
			return StartOf(syFol);
		}
	}


	void Dafny() {
		List<MemberDecl/*!*/> membersDefaultClass = new List<MemberDecl/*!*/>();
		// to support multiple files, create a default module only if theModule is null
		DefaultModuleDecl defaultModule = (DefaultModuleDecl)((LiteralModuleDecl)theModule).ModuleDef;
		// theModule should be a DefaultModuleDecl (actually, the singular DefaultModuleDecl)
		Contract.Assert(defaultModule != null);
		
		while (la.kind == 60) {
			Get();
			Expect(20);
			{
			 string parsedFile = scanner.FullFilename;
			 bool isVerbatimString;
			 string includedFile = Util.RemoveParsedStringQuotes(t.val, out isVerbatimString);
			 includedFile = Util.RemoveEscaping(includedFile, isVerbatimString);
			 string fullPath = includedFile;
			 if (!Path.IsPathRooted(includedFile)) {
			   string basePath = Path.GetDirectoryName(parsedFile);
			   includedFile = Path.Combine(basePath, includedFile);
			   fullPath = Path.GetFullPath(includedFile);
			 }
			 defaultModule.Includes.Add(new Include(t, includedFile, fullPath));
			}
			
		}
		while (StartOf(1)) {
			TopDecl(defaultModule, membersDefaultClass, /* isTopLevel */ true, /* isAbstract */ false);
		}
		DefaultClassDecl defaultClass = null;
		foreach (TopLevelDecl topleveldecl in defaultModule.TopLevelDecls) {
		 defaultClass = topleveldecl as DefaultClassDecl;
		 if (defaultClass != null) {
		   defaultClass.Members.AddRange(membersDefaultClass);
		   break;
		 }
		}
		if (defaultClass == null) { // create the default class here, because it wasn't found
		 defaultClass = new DefaultClassDecl(defaultModule, membersDefaultClass);
		 defaultModule.TopLevelDecls.Add(defaultClass);
		} 
		Expect(0);
	}

	void TopDecl(ModuleDefinition module, List<MemberDecl/*!*/> membersDefaultClass, bool isTopLevel, bool isAbstract ) {
		DeclModifierData dmod = new DeclModifierData(); ModuleDecl submodule;
		ClassDecl/*!*/ c; DatatypeDecl/*!*/ dt; TopLevelDecl td; IteratorDecl iter;
		TraitDecl/*!*/ trait;
		
		while (StartOf(2)) {
			DeclModifier(ref dmod);
		}
		switch (la.kind) {
		case 66: case 69: case 74: {
			SubModuleDecl(dmod, module, out submodule);
			module.TopLevelDecls.Add(submodule); 
			break;
		}
		case 78: {
			ClassDecl(dmod, module, out c);
			module.TopLevelDecls.Add(c); 
			break;
		}
		case 80: case 81: {
			DatatypeDecl(dmod, module, out dt);
			module.TopLevelDecls.Add(dt); 
			break;
		}
		case 83: {
			NewtypeDecl(dmod, module, out td);
			module.TopLevelDecls.Add(td); 
			break;
		}
		case 84: {
			OtherTypeDecl(dmod, module, out td);
			module.TopLevelDecls.Add(td); 
			break;
		}
		case 85: {
			IteratorDecl(dmod, module, out iter);
			module.TopLevelDecls.Add(iter); 
			break;
		}
		case 79: {
			TraitDecl(dmod, module, out trait);
			module.TopLevelDecls.Add(trait); 
			break;
		}
		case 38: case 39: case 40: case 41: case 42: case 82: case 88: case 89: case 90: case 91: {
			ClassMemberDecl(dmod, membersDefaultClass, false, !DafnyOptions.O.AllowGlobals, 
!isTopLevel && DafnyOptions.O.IronDafny && isAbstract);
			break;
		}
		default: SynErr(143); break;
		}
	}

	void DeclModifier(ref DeclModifierData dmod) {
		if (la.kind == 61) {
			Get();
			dmod.IsAbstract = true;  CheckAndSetToken(ref dmod.AbstractToken); 
		} else if (la.kind == 62) {
			Get();
			dmod.IsGhost = true;  CheckAndSetToken(ref dmod.GhostToken); 
		} else if (la.kind == 63) {
			Get();
			dmod.IsStatic = true; CheckAndSetToken(ref dmod.StaticToken); 
		} else if (la.kind == 64) {
			Get();
			dmod.IsProtected = true; CheckAndSetToken(ref dmod.ProtectedToken); 
		} else if (la.kind == 65) {
			Get();
			dmod.IsExtern = true; CheckAndSetToken(ref dmod.ExternToken); 
			if (la.kind == 20) {
				Get();
				bool isVerbatimString;
				string s = Util.RemoveParsedStringQuotes(t.val, out isVerbatimString);
				dmod.ExternName = new StringLiteralExpr(t, s, isVerbatimString);
				
			}
		} else SynErr(144);
	}

	void SubModuleDecl(DeclModifierData dmod, ModuleDefinition parent, out ModuleDecl submodule) {
		Attributes attrs = null;  IToken/*!*/ id;
		List<MemberDecl/*!*/> namedModuleDefaultClassMembers = new List<MemberDecl>();;
		List<IToken> idRefined = null, idPath = null, idAssignment = null;
		ModuleDefinition module;
		submodule = null; // appease compiler
		bool isAbstract = dmod.IsAbstract;
		bool isExclusively = false;
		bool opened = false;
		CheckDeclModifiers(dmod, "Modules", AllowedDeclModifiers.Abstract | AllowedDeclModifiers.Extern);
		
		if (la.kind == 66) {
			Get();
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			EncodeExternAsAttribute(dmod, ref attrs, id, /* needAxiom */ false); 
			if (la.kind == 67 || la.kind == 68) {
				if (la.kind == 67) {
					Get();
					Expect(68);
					QualifiedModuleName(out idRefined);
					isExclusively = true; 
				} else {
					Get();
					QualifiedModuleName(out idRefined);
					isExclusively = false; 
				}
			}
			module = new ModuleDefinition(id, id.val, isAbstract, false, isExclusively, idRefined == null ? null : idRefined, parent, attrs, false, this); 
			Expect(46);
			module.BodyStartTok = t; 
			while (StartOf(1)) {
				TopDecl(module, namedModuleDefaultClassMembers, /* isTopLevel */ false, isAbstract);
			}
			Expect(47);
			module.BodyEndTok = t;
			module.TopLevelDecls.Add(new DefaultClassDecl(module, namedModuleDefaultClassMembers));
			submodule = new LiteralModuleDecl(module, parent); 
		} else if (la.kind == 69) {
			Get();
			if (la.kind == 70) {
				Get();
				opened = true;
			}
			NoUSIdent(out id);
			EncodeExternAsAttribute(dmod, ref attrs, id, /* needAxiom */ false); 
			if (StartOf(3)) {
				if (la.kind == 71) {
					Get();
					QualifiedModuleName(out idPath);
					submodule = new AliasModuleDecl(idPath, id, parent, opened); 
				} else if (la.kind == 72) {
					Get();
					QualifiedModuleName(out idPath);
					if (la.kind == 73) {
						Get();
						QualifiedModuleName(out idAssignment);
					}
					submodule = new ModuleFacadeDecl(idPath, id, parent, idAssignment, opened); 
					errors.Warning(t, "\"import A as B\" has been deprecated; in the new syntax, it is \"import A:B\"");
					
				} else if (la.kind == 21) {
					Get();
					QualifiedModuleName(out idPath);
					submodule = new ModuleFacadeDecl(idPath, id, parent, idAssignment, opened); 
				} else {
					Get();
					QualifiedModuleName(out idPath);
					idPath.Insert(0, id);
					submodule = new AliasModuleDecl(idPath, id, parent, opened); 
					
				}
			}
			if (la.kind == 28) {
				while (!(la.kind == 0 || la.kind == 28)) {SynErr(145); Get();}
				Get();
				errors.Warning(t, "the semi-colon that used to terminate a sub-module declaration has been deprecated; in the new syntax, just leave off the semi-colon"); 
			}
			if (submodule == null) {
			 idPath = new List<IToken>();
			 idPath.Add(id);
			 submodule = new AliasModuleDecl(idPath, id, parent, opened);
			}
			
		} else if (la.kind == 74) {
			IToken exportId;
			List<ExportSignature> exports = new List<ExportSignature>();;
			  List<string> extends = new List<string>(); 
			
			Get();
			NoUSIdent(out exportId);
			while (la.kind == 75 || la.kind == 76 || la.kind == 77) {
				if (la.kind == 75) {
					Get();
					NoUSIdent(out id);
					exports.Add(new ExportSignature(id, false)); 
					while (la.kind == 22) {
						Get();
						NoUSIdent(out id);
						exports.Add(new ExportSignature(id, false)); 
					}
				} else if (la.kind == 76) {
					Get();
					NoUSIdent(out id);
					exports.Add(new ExportSignature(id, true)); 
					while (la.kind == 22) {
						Get();
						NoUSIdent(out id);
						exports.Add(new ExportSignature(id, true)); 
					}
				} else {
					Get();
					NoUSIdent(out id);
					extends.Add(id.val); 
					while (la.kind == 22) {
						Get();
						NoUSIdent(out id);
						extends.Add(id.val); 
					}
				}
			}
			submodule = new ModuleExportDecl(exportId, parent, exports, extends);
			
		} else SynErr(146);
	}

	void ClassDecl(DeclModifierData dmodClass, ModuleDefinition/*!*/ module, out ClassDecl/*!*/ c) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ id;
		Type trait = null;
		List<Type>/*!*/ traits = new List<Type>();
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		CheckDeclModifiers(dmodClass, "Classes", AllowedDeclModifiers.Extern);
		DeclModifierData dmod; 
		
		while (!(la.kind == 0 || la.kind == 78)) {SynErr(147); Get();}
		Expect(78);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		EncodeExternAsAttribute(dmodClass, ref attrs, id, /* needAxiom */ false); 
		if (la.kind == 52) {
			GenericParameters(typeArgs);
		}
		if (la.kind == 77) {
			Get();
			Type(out trait);
			traits.Add(trait); 
			while (la.kind == 22) {
				Get();
				Type(out trait);
				traits.Add(trait); 
			}
		}
		Expect(46);
		bodyStart = t;  
		while (StartOf(4)) {
			dmod = new DeclModifierData(); 
			while (StartOf(2)) {
				DeclModifier(ref dmod);
			}
			ClassMemberDecl(dmod, members, true, false, false);
		}
		Expect(47);
		c = new ClassDecl(id, id.val, module, typeArgs, members, attrs, traits);
		c.BodyStartTok = bodyStart;
		c.BodyEndTok = t;
		
	}

	void DatatypeDecl(DeclModifierData dmod, ModuleDefinition/*!*/ module, out DatatypeDecl/*!*/ dt) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out dt)!=null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<DatatypeCtor/*!*/> ctors = new List<DatatypeCtor/*!*/>();
		IToken bodyStart = Token.NoToken;  // dummy assignment
		bool co = false;
		CheckDeclModifiers(dmod, "Datatypes or codatatypes", AllowedDeclModifiers.None);
		
		while (!(la.kind == 0 || la.kind == 80 || la.kind == 81)) {SynErr(148); Get();}
		if (la.kind == 80) {
			Get();
		} else if (la.kind == 81) {
			Get();
			co = true; 
		} else SynErr(149);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 52) {
			GenericParameters(typeArgs);
		}
		Expect(71);
		bodyStart = t; 
		DatatypeMemberDecl(ctors);
		while (la.kind == 23) {
			Get();
			DatatypeMemberDecl(ctors);
		}
		if (la.kind == 28) {
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(150); Get();}
			Get();
			errors.Warning(t, "the semi-colon that used to terminate a (co)datatype declaration has been deprecated; in the new syntax, just leave off the semi-colon"); 
		}
		if (co) {
		 dt = new CoDatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		} else {
		 dt = new IndDatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		}
		dt.BodyStartTok = bodyStart;
		dt.BodyEndTok = t;
		
	}

	void NewtypeDecl(DeclModifierData dmod, ModuleDefinition module, out TopLevelDecl td) {
		IToken id, bvId;
		Attributes attrs = null;
		td = null;
		Type baseType = null;
		Expression wh;
		CheckDeclModifiers(dmod, "Newtypes", AllowedDeclModifiers.None);
		
		Expect(83);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		Expect(71);
		if (IsIdentColonOrBar()) {
			NoUSIdent(out bvId);
			if (la.kind == 21) {
				Get();
				Type(out baseType);
			}
			if (baseType == null) { baseType = new OperationTypeProxy(true, true, false, false, false, false); } 
			Expect(23);
			Expression(out wh, false, true);
			td = new NewtypeDecl(theVerifyThisFile ? id : new IncludeToken(id), id.val, module, new BoundVar(bvId, bvId.val, baseType), wh, attrs); 
		} else if (StartOf(5)) {
			Type(out baseType);
			td = new NewtypeDecl(theVerifyThisFile ? id : new IncludeToken(id), id.val, module, baseType, attrs); 
		} else SynErr(151);
	}

	void OtherTypeDecl(DeclModifierData dmod, ModuleDefinition module, out TopLevelDecl td) {
		IToken id;
		Attributes attrs = null;
		var eqSupport = TypeParameter.EqualitySupportValue.Unspecified;
		var typeArgs = new List<TypeParameter>();
		td = null;
		Type ty;
		CheckDeclModifiers(dmod, "Type aliases", AllowedDeclModifiers.None);
		
		Expect(84);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 50) {
			Get();
			Expect(54);
			Expect(51);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
			if (la.kind == 52) {
				GenericParameters(typeArgs);
			}
		} else if (StartOf(6)) {
			if (la.kind == 52) {
				GenericParameters(typeArgs);
			}
			if (la.kind == 71) {
				Get();
				Type(out ty);
				td = new TypeSynonymDecl(id, id.val, typeArgs, module, ty, attrs); 
			}
		} else SynErr(152);
		if (td == null) {
		 td = new OpaqueTypeDecl(id, id.val, module, eqSupport, typeArgs, attrs);
		}
		
		if (la.kind == 28) {
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(153); Get();}
			Get();
			errors.Warning(t, "the semi-colon that used to terminate an opaque-type declaration has been deprecated; in the new syntax, just leave off the semi-colon"); 
		}
	}

	void IteratorDecl(DeclModifierData dmod, ModuleDefinition module, out IteratorDecl/*!*/ iter) {
		Contract.Ensures(Contract.ValueAtReturn(out iter) != null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/>/*!*/ typeArgs = new List<TypeParameter/*!*/>();
		List<Formal/*!*/> ins = new List<Formal/*!*/>();
		List<Formal/*!*/> outs = new List<Formal/*!*/>();
		List<FrameExpression/*!*/> reads = new List<FrameExpression/*!*/>();
		List<FrameExpression/*!*/> mod = new List<FrameExpression/*!*/>();
		List<Expression/*!*/> decreases = new List<Expression>();
		List<MaybeFreeExpression/*!*/> req = new List<MaybeFreeExpression/*!*/>();
		List<MaybeFreeExpression/*!*/> ens = new List<MaybeFreeExpression/*!*/>();
		List<MaybeFreeExpression/*!*/> yieldReq = new List<MaybeFreeExpression/*!*/>();
		List<MaybeFreeExpression/*!*/> yieldEns = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> dec = new List<Expression/*!*/>();
		Attributes readsAttrs = null;
		Attributes modAttrs = null;
		Attributes decrAttrs = null;
		BlockStmt body = null;
		IToken signatureEllipsis = null;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		CheckDeclModifiers(dmod, "Iterators", AllowedDeclModifiers.None);
		
		while (!(la.kind == 0 || la.kind == 85)) {SynErr(154); Get();}
		Expect(85);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 50 || la.kind == 52) {
			if (la.kind == 52) {
				GenericParameters(typeArgs);
			}
			Formals(true, true, ins);
			if (la.kind == 86 || la.kind == 87) {
				if (la.kind == 86) {
					Get();
				} else {
					Get();
					SemErr(t, "iterators don't have a 'returns' clause; did you mean 'yields'?"); 
				}
				Formals(false, true, outs);
			}
		} else if (la.kind == 59) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(155);
		while (StartOf(7)) {
			IteratorSpec(reads, mod, decreases, req, ens, yieldReq, yieldEns, ref readsAttrs, ref modAttrs, ref decrAttrs);
		}
		if (la.kind == 46) {
			BlockStmt(out body, out bodyStart, out bodyEnd);
		}
		iter = new IteratorDecl(id, id.val, module, typeArgs, ins, outs,
		                       new Specification<FrameExpression>(reads, readsAttrs),
		                       new Specification<FrameExpression>(mod, modAttrs),
		                       new Specification<Expression>(decreases, decrAttrs),
		                       req, ens, yieldReq, yieldEns,
		                       body, attrs, signatureEllipsis);
		iter.BodyStartTok = bodyStart;
		iter.BodyEndTok = bodyEnd;
		
	}

	void TraitDecl(DeclModifierData dmodIn, ModuleDefinition/*!*/ module, out TraitDecl/*!*/ trait) {
		Contract.Requires(module != null);     
		Contract.Ensures(Contract.ValueAtReturn(out trait) != null);
		CheckDeclModifiers(dmodIn, "Traits", AllowedDeclModifiers.None);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>(); //traits should not support type parameters at the moment
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		DeclModifierData dmod; 
		
		while (!(la.kind == 0 || la.kind == 79)) {SynErr(156); Get();}
		Expect(79);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 52) {
			GenericParameters(typeArgs);
		}
		Expect(46);
		bodyStart = t; 
		while (StartOf(4)) {
			dmod  = new DeclModifierData(); 
			while (StartOf(2)) {
				DeclModifier(ref dmod);
			}
			ClassMemberDecl(dmod, members, true, false, false);
		}
		Expect(47);
		trait = new TraitDecl(id, id.val, module, typeArgs, members, attrs);
		trait.BodyStartTok = bodyStart;
		trait.BodyEndTok = t;
		
	}

	void ClassMemberDecl(DeclModifierData dmod, List<MemberDecl> mm, bool allowConstructors, bool moduleLevelDecl, bool isWithinAbstractModule) {
		Contract.Requires(cce.NonNullElements(mm));
		Method/*!*/ m;
		Function/*!*/ f;
		
		if (la.kind == 82) {
			if (moduleLevelDecl) {
			 SemErr(la, "fields are not allowed to be declared at the module level; instead, wrap the field in a 'class' declaration");
			 dmod.IsStatic = false;
			}
			
			FieldDecl(dmod, mm);
		} else if (IsFunctionDecl()) {
			if (moduleLevelDecl && dmod.StaticToken != null) {
			 errors.Warning(dmod.StaticToken, "module-level functions are always non-instance, so the 'static' keyword is not allowed here");
			 dmod.IsStatic = false;
			}
			
			FunctionDecl(dmod, isWithinAbstractModule, out f);
			mm.Add(f); 
		} else if (StartOf(8)) {
			if (moduleLevelDecl && dmod.StaticToken != null) {
			 errors.Warning(dmod.StaticToken, "module-level methods are always non-instance, so the 'static' keyword is not allowed here");
			 dmod.IsStatic = false;
			}
			
			MethodDecl(dmod, allowConstructors, isWithinAbstractModule, out m);
			mm.Add(m); 
		} else SynErr(157);
	}

	void Attribute(ref Attributes attrs) {
		IToken openBrace, colon, closeBrace;
		IToken x = null;
		var args = new List<Expression>();
		
		Expect(46);
		openBrace = t; 
		Expect(21);
		colon = t; 
		ConvertKeywordTokenToIdent(); 
		NoUSIdent(out x);
		if (StartOf(9)) {
			Expressions(args);
		}
		Expect(47);
		closeBrace = t; 
		attrs = new UserSuppliedAttributes(x, openBrace, colon, closeBrace, args, attrs); 
	}

	void NoUSIdent(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t;
		if (x.val.StartsWith("_")) {
		 SemErr("cannot declare identifier beginning with underscore");
		}
		
	}

	void QualifiedModuleName(out List<IToken> ids) {
		IToken id; ids = new List<IToken>(); 
		Ident(out id);
		ids.Add(id); 
		while (la.kind == 27) {
			Get();
			Ident(out id);
			ids.Add(id); 
		}
	}

	void Ident(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t; 
	}

	void GenericParameters(List<TypeParameter/*!*/>/*!*/ typeArgs) {
		Contract.Requires(cce.NonNullElements(typeArgs));
		IToken/*!*/ id;
		TypeParameter.EqualitySupportValue eqSupport;
		
		Expect(52);
		NoUSIdent(out id);
		eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
		if (la.kind == 50) {
			Get();
			Expect(54);
			Expect(51);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
		}
		typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		while (la.kind == 22) {
			Get();
			NoUSIdent(out id);
			eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
			if (la.kind == 50) {
				Get();
				Expect(54);
				Expect(51);
				eqSupport = TypeParameter.EqualitySupportValue.Required; 
			}
			typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		}
		Expect(53);
	}

	void Type(out Type ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; 
		TypeAndToken(out tok, out ty);
	}

	void FieldDecl(DeclModifierData dmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		IToken/*!*/ id;  Type/*!*/ ty;
		CheckDeclModifiers(dmod, "Fields", AllowedDeclModifiers.Ghost);
		
		while (!(la.kind == 0 || la.kind == 82)) {SynErr(158); Get();}
		Expect(82);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		FIdentType(out id, out ty);
		mm.Add(new Field(id, id.val, dmod.IsGhost, ty, attrs)); 
		while (la.kind == 22) {
			Get();
			FIdentType(out id, out ty);
			mm.Add(new Field(id, id.val, dmod.IsGhost, ty, attrs)); 
		}
		OldSemi();
	}

	void FunctionDecl(DeclModifierData dmod, bool isWithinAbstractModule, out Function/*!*/ f) {
		Contract.Ensures(Contract.ValueAtReturn(out f)!=null);
		Attributes attrs = null;
		IToken/*!*/ id = Token.NoToken;  // to please compiler
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<Formal/*!*/> formals = new List<Formal/*!*/>();
		Type/*!*/ returnType = new BoolType();
		List<Expression/*!*/> reqs = new List<Expression/*!*/>();
		List<Expression/*!*/> ens = new List<Expression/*!*/>();
		List<FrameExpression/*!*/> reads = new List<FrameExpression/*!*/>();
		List<Expression/*!*/> decreases;
		Expression body = null;
		bool isPredicate = false; bool isIndPredicate = false; bool isCoPredicate = false;
		bool isFunctionMethod = false;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		IToken signatureEllipsis = null;
		bool missingOpenParen;
		
		if (la.kind == 38) {
			Get();
			if (la.kind == 88) {
				Get();
				isFunctionMethod = true; 
			}
			AllowedDeclModifiers allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static | AllowedDeclModifiers.Protected;
			string caption = "Functions";
			if (isFunctionMethod) { 
			 allowed |= AllowedDeclModifiers.Extern; 
			 caption = "Function methods";
			}
			CheckDeclModifiers(dmod, caption, allowed);
			
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 50 || la.kind == 52) {
				if (la.kind == 52) {
					GenericParameters(typeArgs);
				}
				Formals(true, isFunctionMethod, formals);
				Expect(21);
				Type(out returnType);
			} else if (la.kind == 59) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(159);
		} else if (la.kind == 39) {
			Get();
			isPredicate = true; 
			if (la.kind == 88) {
				Get();
				isFunctionMethod = true; 
			}
			AllowedDeclModifiers allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static | AllowedDeclModifiers.Protected;
			string caption = "Predicates";
			if (isFunctionMethod) { 
			 allowed |= AllowedDeclModifiers.Extern; 
			 caption = "Predicate methods";
			}
			CheckDeclModifiers(dmod, caption, allowed);
			
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (StartOf(10)) {
				if (la.kind == 52) {
					GenericParameters(typeArgs);
				}
				missingOpenParen = true; 
				if (la.kind == 50) {
					Formals(true, isFunctionMethod, formals);
					missingOpenParen = false; 
				}
				if (missingOpenParen) { errors.Warning(t, "with the new support of higher-order functions in Dafny, parentheses-less predicates are no longer supported; in the new syntax, parentheses are required for the declaration and uses of predicates, even if the predicate takes no additional arguments"); } 
				if (la.kind == 21) {
					Get();
					SemErr(t, "predicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 59) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(160);
		} else if (la.kind == 40) {
			Get();
			Expect(39);
			isIndPredicate = true; 
			CheckDeclModifiers(dmod, "Inductive predicates",
			 AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static | AllowedDeclModifiers.Protected);
			
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 50 || la.kind == 52) {
				if (la.kind == 52) {
					GenericParameters(typeArgs);
				}
				Formals(true, isFunctionMethod, formals);
				if (la.kind == 21) {
					Get();
					SemErr(t, "inductive predicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 59) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(161);
		} else if (la.kind == 42) {
			Get();
			isCoPredicate = true; 
			CheckDeclModifiers(dmod, "Copredicates",
			 AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static | AllowedDeclModifiers.Protected);
			
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 50 || la.kind == 52) {
				if (la.kind == 52) {
					GenericParameters(typeArgs);
				}
				Formals(true, isFunctionMethod, formals);
				if (la.kind == 21) {
					Get();
					SemErr(t, "copredicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 59) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(162);
		} else SynErr(163);
		decreases = isIndPredicate || isCoPredicate ? null : new List<Expression/*!*/>(); 
		while (StartOf(11)) {
			FunctionSpec(reqs, reads, ens, decreases);
		}
		if (la.kind == 46) {
			FunctionBody(out body, out bodyStart, out bodyEnd);
		}
		if (!isWithinAbstractModule && DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 &&
		   !Attributes.Contains(attrs, "axiom") && !Attributes.Contains(attrs, "imported")) {
		  SemErr(t, "a function with an ensures clause must have a body, unless given the :axiom attribute");
		}
		EncodeExternAsAttribute(dmod, ref attrs, id, /* needAxiom */ true);
		IToken tok = theVerifyThisFile ? id : new IncludeToken(id);
		if (isPredicate) {
		  f = new Predicate(tok, id.val, dmod.IsStatic, dmod.IsProtected, !isFunctionMethod, typeArgs, formals,
		                    reqs, reads, ens, new Specification<Expression>(decreases, null), body, Predicate.BodyOriginKind.OriginalOrInherited, attrs, signatureEllipsis);
		} else if (isIndPredicate) {
		  f = new InductivePredicate(tok, id.val, dmod.IsStatic, dmod.IsProtected, typeArgs, formals,
		                             reqs, reads, ens, body, attrs, signatureEllipsis);
		} else if (isCoPredicate) {
		  f = new CoPredicate(tok, id.val, dmod.IsStatic, dmod.IsProtected, typeArgs, formals,
		                      reqs, reads, ens, body, attrs, signatureEllipsis);
		} else {
		  f = new Function(tok, id.val, dmod.IsStatic, dmod.IsProtected, !isFunctionMethod, typeArgs, formals, returnType,
		                   reqs, reads, ens, new Specification<Expression>(decreases, null), body, attrs, signatureEllipsis);
		}
		f.BodyStartTok = bodyStart;
		f.BodyEndTok = bodyEnd;
		theBuiltIns.CreateArrowTypeDecl(formals.Count);
		if (isIndPredicate || isCoPredicate) {
		 // also create an arrow type for the corresponding prefix predicate
		 theBuiltIns.CreateArrowTypeDecl(formals.Count + 1);
		}
		
	}

	void MethodDecl(DeclModifierData dmod, bool allowConstructor, bool isWithinAbstractModule, out Method/*!*/ m) {
		Contract.Ensures(Contract.ValueAtReturn(out m) !=null);
		IToken/*!*/ id = Token.NoToken;
		bool hasName = false;  IToken keywordToken;
		Attributes attrs = null;
		List<TypeParameter/*!*/>/*!*/ typeArgs = new List<TypeParameter/*!*/>();
		List<Formal/*!*/> ins = new List<Formal/*!*/>();
		List<Formal/*!*/> outs = new List<Formal/*!*/>();
		List<MaybeFreeExpression/*!*/> req = new List<MaybeFreeExpression/*!*/>();
		List<FrameExpression/*!*/> mod = new List<FrameExpression/*!*/>();
		List<MaybeFreeExpression/*!*/> ens = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> dec = new List<Expression/*!*/>();
		Attributes decAttrs = null;
		Attributes modAttrs = null;
		BlockStmt body = null;
		bool isLemma = false;
		bool isConstructor = false;
		bool isIndLemma = false;
		bool isCoLemma = false;
		IToken signatureEllipsis = null;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		AllowedDeclModifiers allowed = AllowedDeclModifiers.None;
		string caption = "";
		
		while (!(StartOf(12))) {SynErr(164); Get();}
		switch (la.kind) {
		case 88: {
			Get();
			caption = "Methods";
			allowed = AllowedDeclModifiers.Ghost | AllowedDeclModifiers.Static 
			 | AllowedDeclModifiers.Extern; 
			break;
		}
		case 41: {
			Get();
			isLemma = true; caption = "Lemmas";
			allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static 
			 | AllowedDeclModifiers.Protected; 
			break;
		}
		case 89: {
			Get();
			isCoLemma = true; caption = "Colemmas";
			allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static 
			 | AllowedDeclModifiers.Protected; 
			break;
		}
		case 90: {
			Get();
			isCoLemma = true; caption = "Comethods";
			allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static 
			 | AllowedDeclModifiers.Protected;
			errors.Warning(t, "the 'comethod' keyword has been deprecated; it has been renamed to 'colemma'");
			
			break;
		}
		case 40: {
			Get();
			Expect(41);
			isIndLemma = true;  caption = "Inductive lemmas";
			allowed = AllowedDeclModifiers.AlreadyGhost | AllowedDeclModifiers.Static;
			break;
		}
		case 91: {
			Get();
			if (allowConstructor) {
			 isConstructor = true;
			} else {
			 SemErr(t, "constructors are allowed only in classes");
			} 
			caption = "Constructors";
			allowed = AllowedDeclModifiers.None;
			
			break;
		}
		default: SynErr(165); break;
		}
		keywordToken = t; 
		CheckDeclModifiers(dmod, caption, allowed); 
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		if (la.kind == 1) {
			NoUSIdent(out id);
			hasName = true; 
		}
		if (!hasName) {
		 id = keywordToken;
		 if (!isConstructor) {
		   SemErr(la, "a method must be given a name (expecting identifier)");
		 }
		}
		EncodeExternAsAttribute(dmod, ref attrs, id, /* needAxiom */ true);
		
		if (la.kind == 50 || la.kind == 52) {
			if (la.kind == 52) {
				GenericParameters(typeArgs);
			}
			Formals(true, !dmod.IsGhost, ins);
			if (la.kind == 87) {
				Get();
				if (isConstructor) { SemErr(t, "constructors cannot have out-parameters"); } 
				Formals(false, !dmod.IsGhost, outs);
			}
		} else if (la.kind == 59) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(166);
		while (StartOf(13)) {
			MethodSpec(req, mod, ens, dec, ref decAttrs, ref modAttrs);
		}
		if (la.kind == 46) {
			BlockStmt(out body, out bodyStart, out bodyEnd);
		}
		if (!isWithinAbstractModule && DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 && !Attributes.Contains(attrs, "axiom") && !Attributes.Contains(attrs, "imported") && !Attributes.Contains(attrs, "decl") && theVerifyThisFile) {
		  SemErr(t, "a method with an ensures clause must have a body, unless given the :axiom attribute");
		}
		
		IToken tok = theVerifyThisFile ? id : new IncludeToken(id);
		if (isConstructor) {
		 m = new Constructor(tok, hasName ? id.val : "_ctor", typeArgs, ins,
		                     req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else if (isIndLemma) {
		 m = new InductiveLemma(tok, id.val, dmod.IsStatic, typeArgs, ins, outs,
		                        req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else if (isCoLemma) {
		 m = new CoLemma(tok, id.val, dmod.IsStatic, typeArgs, ins, outs,
		                 req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else if (isLemma) {
		 m = new Lemma(tok, id.val, dmod.IsStatic, typeArgs, ins, outs,
		               req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else {
		 m = new Method(tok, id.val, dmod.IsStatic, dmod.IsGhost, typeArgs, ins, outs,
		                req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		}
		m.BodyStartTok = bodyStart;
		m.BodyEndTok = bodyEnd;
		
	}

	void DatatypeMemberDecl(List<DatatypeCtor/*!*/>/*!*/ ctors) {
		Contract.Requires(cce.NonNullElements(ctors));
		Attributes attrs = null;
		IToken/*!*/ id;
		List<Formal/*!*/> formals = new List<Formal/*!*/>();
		
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 50) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(50);
		if (StartOf(14)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 22) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(51);
	}

	void FIdentType(out IToken/*!*/ id, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		id = Token.NoToken;
		
		if (la.kind == 1) {
			WildIdent(out id, false);
		} else if (la.kind == 2) {
			Get();
			id = t; 
		} else SynErr(167);
		Expect(21);
		Type(out ty);
	}

	void OldSemi() {
		if (la.kind == 28) {
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(168); Get();}
			Get();
		}
	}

	void Expression(out Expression e, bool allowSemi, bool allowLambda) {
		Expression e0; IToken endTok; 
		EquivExpression(out e, allowSemi, allowLambda);
		if (SemiFollowsCall(allowSemi, e)) {
			Expect(28);
			endTok = t; 
			Expression(out e0, allowSemi, allowLambda);
			e = new StmtExpr(e.tok,
			     new UpdateStmt(e.tok, endTok, new List<Expression>(), new List<AssignmentRhs>() { new ExprRhs(e, null) }),
			     e0);
			
		}
	}

	void GIdentType(bool allowGhostKeyword, out IToken/*!*/ id, out Type/*!*/ ty, out bool isGhost) {
		Contract.Ensures(Contract.ValueAtReturn(out id)!=null);
		Contract.Ensures(Contract.ValueAtReturn(out ty)!=null);
		isGhost = false; 
		if (la.kind == 62) {
			Get();
			if (allowGhostKeyword) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
		}
		IdentType(out id, out ty, true);
	}

	void IdentType(out IToken/*!*/ id, out Type/*!*/ ty, bool allowWildcardId) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		WildIdent(out id, allowWildcardId);
		Expect(21);
		Type(out ty);
	}

	void WildIdent(out IToken x, bool allowWildcardId) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t;
		t.val = UnwildIdent(t.val, allowWildcardId);
		
	}

	void LocalIdentTypeOptional(out LocalVariable var, bool isGhost) {
		IToken id;  Type ty;  Type optType = null;
		
		WildIdent(out id, true);
		if (la.kind == 21) {
			Get();
			Type(out ty);
			optType = ty; 
		}
		var = new LocalVariable(id, id, id.val, optType == null ? new InferredTypeProxy() : optType, isGhost); 
	}

	void IdentTypeOptional(out BoundVar var) {
		Contract.Ensures(Contract.ValueAtReturn(out var) != null);
		IToken id;  Type ty;  Type optType = null;
		
		WildIdent(out id, true);
		if (la.kind == 21) {
			Get();
			Type(out ty);
			optType = ty; 
		}
		var = new BoundVar(id, id.val, optType == null ? new InferredTypeProxy() : optType); 
	}

	void TypeIdentOptional(out IToken/*!*/ id, out string/*!*/ identName, out Type/*!*/ ty, out bool isGhost) {
		Contract.Ensures(Contract.ValueAtReturn(out id)!=null);
		Contract.Ensures(Contract.ValueAtReturn(out ty)!=null);
		Contract.Ensures(Contract.ValueAtReturn(out identName)!=null);
		string name = null; id = Token.NoToken; ty = new BoolType()/*dummy*/; isGhost = false; 
		if (la.kind == 62) {
			Get();
			isGhost = true; 
		}
		if (StartOf(5)) {
			TypeAndToken(out id, out ty);
			if (la.kind == 21) {
				Get();
				UserDefinedType udt = ty as UserDefinedType;
				if (udt != null && udt.TypeArgs.Count == 0) {
				 name = udt.Name;
				} else {
				 SemErr(id, "invalid formal-parameter name in datatype constructor");
				}
				
				Type(out ty);
			}
		} else if (la.kind == 2) {
			Get();
			id = t; name = id.val;
			Expect(21);
			Type(out ty);
		} else SynErr(169);
		if (name != null) {
		 identName = name;
		} else {
		 identName = "#" + anonymousIds++;
		}
		
	}

	void TypeAndToken(out IToken tok, out Type ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok)!=null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type> gt; List<Type> tupleArgTypes = null;
		
		switch (la.kind) {
		case 6: {
			Get();
			tok = t; 
			break;
		}
		case 7: {
			Get();
			tok = t;  ty = new CharType(); 
			break;
		}
		case 9: {
			Get();
			tok = t;  ty = new NatType(); 
			break;
		}
		case 8: {
			Get();
			tok = t;  ty = new IntType(); 
			break;
		}
		case 10: {
			Get();
			tok = t;  ty = new RealType(); 
			break;
		}
		case 11: {
			Get();
			tok = t;  ty = new ObjectType(); 
			break;
		}
		case 13: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("set type expects only one type argument");
			}
			ty = new SetType(true, gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 14: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("set type expects only one type argument");
			}
			ty = new SetType(false, gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 15: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("multiset type expects only one type argument");
			}
			ty = new MultiSetType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 16: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("seq type expects only one type argument");
			}
			ty = new SeqType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 12: {
			Get();
			tok = t;  ty = new UserDefinedType(tok, tok.val, null); 
			break;
		}
		case 17: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count == 0) {
			 ty = new MapType(true, null, null);
			} else if (gt.Count != 2) {
			 SemErr("map type expects two type arguments");
			 ty = new MapType(true, gt[0], gt.Count == 1 ? new InferredTypeProxy() : gt[1]);
			} else {
			 ty = new MapType(true, gt[0], gt[1]);
			}
			
			break;
		}
		case 18: {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 52) {
				GenericInstantiation(gt);
			}
			if (gt.Count == 0) {
			 ty = new MapType(false, null, null);
			} else if (gt.Count != 2) {
			 SemErr("imap type expects two type arguments");
			 ty = new MapType(false, gt[0], gt.Count == 1 ? new InferredTypeProxy() : gt[1]);
			} else {
			 ty = new MapType(false, gt[0], gt[1]);
			}
			
			break;
		}
		case 5: {
			Get();
			tok = t;  gt = null; 
			if (la.kind == 52) {
				gt = new List<Type>(); 
				GenericInstantiation(gt);
			}
			int dims = tok.val.Length == 5 ? 1 : int.Parse(tok.val.Substring(5));
			ty = theBuiltIns.ArrayType(tok, dims, gt, true);
			
			break;
		}
		case 50: {
			Get();
			tok = t; tupleArgTypes = new List<Type>(); 
			if (StartOf(5)) {
				Type(out ty);
				tupleArgTypes.Add(ty); 
				while (la.kind == 22) {
					Get();
					Type(out ty);
					tupleArgTypes.Add(ty); 
				}
			}
			Expect(51);
			if (tupleArgTypes.Count == 1) {
			 // just return the type 'ty'
			} else {
			 var dims = tupleArgTypes.Count;
			 var tmp = theBuiltIns.TupleType(tok, dims, true);  // make sure the tuple type exists
			 ty = new UserDefinedType(tok, BuiltIns.TupleTypeName(dims), dims == 0 ? null : tupleArgTypes);
			}
			
			break;
		}
		case 1: {
			Expression e; tok = t; 
			NameSegmentForTypeName(out e);
			tok = t; 
			while (la.kind == 27) {
				Get();
				Expect(1);
				tok = t; List<Type> typeArgs = null; 
				if (la.kind == 52) {
					typeArgs = new List<Type>(); 
					GenericInstantiation(typeArgs);
				}
				e = new ExprDotName(tok, e, tok.val, typeArgs); 
			}
			ty = new UserDefinedType(e.tok, e); 
			break;
		}
		default: SynErr(170); break;
		}
		if (la.kind == 30) {
			Type t2; 
			Get();
			tok = t; 
			Type(out t2);
			if (tupleArgTypes != null) {
			 gt = tupleArgTypes;
			} else {
			 gt = new List<Type>{ ty };
			}
			ty = new ArrowType(tok, gt, t2);
			theBuiltIns.CreateArrowTypeDecl(gt.Count);
			
		}
	}

	void Formals(bool incoming, bool allowGhostKeyword, List<Formal> formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken id;  Type ty;  bool isGhost; 
		Expect(50);
		if (la.kind == 1 || la.kind == 62) {
			GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 22) {
				Get();
				GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(51);
	}

	void IteratorSpec(List<FrameExpression/*!*/>/*!*/ reads, List<FrameExpression/*!*/>/*!*/ mod, List<Expression/*!*/> decreases,
List<MaybeFreeExpression/*!*/>/*!*/ req, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<MaybeFreeExpression/*!*/>/*!*/ yieldReq, List<MaybeFreeExpression/*!*/>/*!*/ yieldEns,
ref Attributes readsAttrs, ref Attributes modAttrs, ref Attributes decrAttrs) {
		Expression/*!*/ e; FrameExpression/*!*/ fe; bool isFree = false; bool isYield = false; Attributes ensAttrs = null;
		
		while (!(StartOf(15))) {SynErr(171); Get();}
		if (la.kind == 44) {
			Get();
			while (IsAttribute()) {
				Attribute(ref readsAttrs);
			}
			FrameExpression(out fe, false, false);
			reads.Add(fe); 
			while (la.kind == 22) {
				Get();
				FrameExpression(out fe, false, false);
				reads.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 43) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, false);
			mod.Add(fe); 
			while (la.kind == 22) {
				Get();
				FrameExpression(out fe, false, false);
				mod.Add(fe); 
			}
			OldSemi();
		} else if (StartOf(16)) {
			if (la.kind == 92) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			if (la.kind == 94) {
				Get();
				isYield = true; 
			}
			if (la.kind == 45) {
				Get();
				Expression(out e, false, false);
				OldSemi();
				if (isYield) {
				 yieldReq.Add(new MaybeFreeExpression(e, isFree));
				} else {
				 req.Add(new MaybeFreeExpression(e, isFree));
				}
				
			} else if (la.kind == 93) {
				Get();
				while (IsAttribute()) {
					Attribute(ref ensAttrs);
				}
				Expression(out e, false, false);
				OldSemi();
				if (isYield) {
				 yieldEns.Add(new MaybeFreeExpression(e, isFree, ensAttrs));
				} else {
				 ens.Add(new MaybeFreeExpression(e, isFree, ensAttrs));
				}
				
			} else SynErr(172);
		} else if (la.kind == 36) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decrAttrs);
			}
			DecreasesList(decreases, false, false);
			OldSemi();
		} else SynErr(173);
	}

	void BlockStmt(out BlockStmt/*!*/ block, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out block) != null);
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(46);
		bodyStart = t; 
		while (StartOf(17)) {
			Stmt(body);
		}
		Expect(47);
		bodyEnd = t;
		block = new BlockStmt(bodyStart, bodyEnd, body); 
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases, ref Attributes decAttrs, ref Attributes modAttrs) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false; Attributes ensAttrs = null;
		
		while (!(StartOf(18))) {SynErr(174); Get();}
		if (la.kind == 43) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, false);
			mod.Add(fe); 
			while (la.kind == 22) {
				Get();
				FrameExpression(out fe, false, false);
				mod.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 45 || la.kind == 92 || la.kind == 93) {
			if (la.kind == 92) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			if (la.kind == 45) {
				Get();
				Expression(out e, false, false);
				OldSemi();
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 93) {
				Get();
				while (IsAttribute()) {
					Attribute(ref ensAttrs);
				}
				Expression(out e, false, false);
				OldSemi();
				ens.Add(new MaybeFreeExpression(e, isFree, ensAttrs)); 
			} else SynErr(175);
		} else if (la.kind == 36) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decAttrs);
			}
			DecreasesList(decreases, true, false);
			OldSemi();
		} else SynErr(176);
	}

	void FrameExpression(out FrameExpression fe, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null);
		Expression/*!*/ e;
		IToken/*!*/ id;
		string fieldName = null;  IToken feTok = null;
		fe = null;
		
		if (StartOf(9)) {
			Expression(out e, allowSemi, allowLambda);
			feTok = e.tok; 
			if (la.kind == 95) {
				Get();
				Ident(out id);
				fieldName = id.val;  feTok = id; 
			}
			fe = new FrameExpression(feTok, e, fieldName); 
		} else if (la.kind == 95) {
			Get();
			Ident(out id);
			fieldName = id.val; 
			fe = new FrameExpression(id, new ImplicitThisExpr(id), fieldName); 
		} else SynErr(177);
	}

	void DecreasesList(List<Expression> decreases, bool allowWildcard, bool allowLambda) {
		Expression e; 
		PossiblyWildExpression(out e, allowLambda);
		if (!allowWildcard && e is WildcardExpr) {
		 SemErr(e.tok, "'decreases *' is allowed only on loops and tail-recursive methods");
		} else {
		 decreases.Add(e);
		}
		
		while (la.kind == 22) {
			Get();
			PossiblyWildExpression(out e, allowLambda);
			if (!allowWildcard && e is WildcardExpr) {
			 SemErr(e.tok, "'decreases *' is allowed only on loops and tail-recursive methods");
			} else {
			 decreases.Add(e);
			}
			
		}
	}

	void GenericInstantiation(List<Type/*!*/>/*!*/ gt) {
		Contract.Requires(cce.NonNullElements(gt)); Type/*!*/ ty; 
		Expect(52);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 22) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(53);
	}

	void NameSegmentForTypeName(out Expression e) {
		IToken id;
		List<Type> typeArgs = null;
		
		Ident(out id);
		if (la.kind == 52) {
			typeArgs = new List<Type>(); 
			GenericInstantiation(typeArgs);
		}
		e = new NameSegment(id, id.val, typeArgs);
		
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/> decreases) {
		Contract.Requires(cce.NonNullElements(reqs));
		Contract.Requires(cce.NonNullElements(reads));
		Contract.Requires(decreases == null || cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		while (!(StartOf(19))) {SynErr(178); Get();}
		if (la.kind == 45) {
			Get();
			Expression(out e, false, false);
			OldSemi();
			reqs.Add(e); 
		} else if (la.kind == 44) {
			Get();
			PossiblyWildFrameExpression(out fe, false);
			reads.Add(fe); 
			while (la.kind == 22) {
				Get();
				PossiblyWildFrameExpression(out fe, false);
				reads.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 93) {
			Get();
			Expression(out e, false, false);
			OldSemi();
			ens.Add(e); 
		} else if (la.kind == 36) {
			Get();
			if (decreases == null) {
			 SemErr(t, "'decreases' clauses are meaningless for copredicates, so they are not allowed");
			 decreases = new List<Expression/*!*/>();
			}
			
			DecreasesList(decreases, false, false);
			OldSemi();
		} else SynErr(179);
	}

	void FunctionBody(out Expression/*!*/ e, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); e = dummyExpr; 
		Expect(46);
		bodyStart = t; 
		Expression(out e, true, true);
		Expect(47);
		bodyEnd = t; 
	}

	void PossiblyWildFrameExpression(out FrameExpression fe, bool allowSemi) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); fe = dummyFrameExpr; 
		if (la.kind == 57) {
			Get();
			fe = new FrameExpression(t, new WildcardExpr(t), null); 
		} else if (StartOf(20)) {
			FrameExpression(out fe, allowSemi, false);
		} else SynErr(180);
	}

	void PossiblyWildExpression(out Expression e, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 57) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(9)) {
			Expression(out e, false, allowLambda);
		} else SynErr(181);
	}

	void Stmt(List<Statement/*!*/>/*!*/ ss) {
		Statement/*!*/ s;
		
		OneStmt(out s);
		ss.Add(s); 
	}

	void OneStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  IToken/*!*/ id;  string label = null;
		s = dummyStmt;  /* to please the compiler */
		BlockStmt bs;
		IToken bodyStart, bodyEnd;
		int breakCount;
		
		while (!(StartOf(21))) {SynErr(182); Get();}
		switch (la.kind) {
		case 46: {
			BlockStmt(out bs, out bodyStart, out bodyEnd);
			s = bs; 
			break;
		}
		case 105: {
			AssertStmt(out s);
			break;
		}
		case 31: {
			AssumeStmt(out s);
			break;
		}
		case 106: {
			PrintStmt(out s);
			break;
		}
		case 1: case 2: case 3: case 4: case 8: case 10: case 19: case 20: case 23: case 50: case 135: case 136: case 137: case 138: case 139: case 140: {
			UpdateStmt(out s);
			break;
		}
		case 62: case 82: {
			VarDeclStatement(out s);
			break;
		}
		case 102: {
			IfStmt(out s);
			break;
		}
		case 103: {
			WhileStmt(out s);
			break;
		}
		case 104: {
			MatchStmt(out s);
			break;
		}
		case 107: case 108: {
			ForallStmt(out s);
			break;
		}
		case 32: {
			CalcStmt(out s);
			break;
		}
		case 109: {
			ModifyStmt(out s);
			break;
		}
		case 96: {
			Get();
			x = t; 
			NoUSIdent(out id);
			Expect(21);
			OneStmt(out s);
			s.Labels = new LList<Label>(new Label(x, id.val), s.Labels); 
			break;
		}
		case 97: {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				NoUSIdent(out id);
				label = id.val; 
			} else if (la.kind == 28 || la.kind == 97) {
				while (la.kind == 97) {
					Get();
					breakCount++; 
				}
			} else SynErr(183);
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(184); Get();}
			Expect(28);
			s = label != null ? new BreakStmt(x, t, label) : new BreakStmt(x, t, breakCount); 
			break;
		}
		case 94: case 100: {
			ReturnStmt(out s);
			break;
		}
		case 59: {
			SkeletonStmt(out s);
			break;
		}
		default: SynErr(185); break;
		}
	}

	void AssertStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;
		Expression e = dummyExpr; Attributes attrs = null;
		IToken dotdotdot = null;
		
		Expect(105);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(9)) {
			Expression(out e, false, true);
		} else if (la.kind == 59) {
			Get();
			dotdotdot = t; 
		} else SynErr(186);
		Expect(28);
		if (dotdotdot != null) {
		 s = new SkeletonStatement(new AssertStmt(x, t, new LiteralExpr(x, true), attrs), dotdotdot, null);
		} else {
		 s = new AssertStmt(x, t, e, attrs);
		}
		
	}

	void AssumeStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;
		Expression e = dummyExpr; Attributes attrs = null;
		IToken dotdotdot = null;
		
		Expect(31);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(9)) {
			Expression(out e, false, true);
		} else if (la.kind == 59) {
			Get();
			dotdotdot = t; 
		} else SynErr(187);
		Expect(28);
		if (dotdotdot != null) {
		 s = new SkeletonStatement(new AssumeStmt(x, t, new LiteralExpr(x, true), attrs), dotdotdot, null);
		} else {
		 s = new AssumeStmt(x, t, e, attrs);
		}
		
	}

	void PrintStmt(out Statement s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		IToken x;  Expression e;
		var args = new List<Expression>();
		
		Expect(106);
		x = t; 
		Expression(out e, false, true);
		args.Add(e); 
		while (la.kind == 22) {
			Get();
			Expression(out e, false, true);
			args.Add(e); 
		}
		Expect(28);
		s = new PrintStmt(x, t, args); 
	}

	void UpdateStmt(out Statement/*!*/ s) {
		List<Expression> lhss = new List<Expression>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		Expression e;  AssignmentRhs r;
		IToken x, endTok = Token.NoToken;
		Attributes attrs = null;
		IToken suchThatAssume = null;
		Expression suchThat = null;
		
		Lhs(out e);
		x = e.tok; 
		if (la.kind == 28 || la.kind == 46) {
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			Expect(28);
			endTok = t; rhss.Add(new ExprRhs(e, attrs)); 
		} else if (la.kind == 22 || la.kind == 25 || la.kind == 99) {
			lhss.Add(e); 
			while (la.kind == 22) {
				Get();
				Lhs(out e);
				lhss.Add(e); 
			}
			if (la.kind == 99) {
				Get();
				x = t; 
				Rhs(out r);
				rhss.Add(r); 
				while (la.kind == 22) {
					Get();
					Rhs(out r);
					rhss.Add(r); 
				}
			} else if (la.kind == 25) {
				Get();
				x = t; 
				if (la.kind == _assume) {
					Expect(31);
					suchThatAssume = t; 
				}
				Expression(out suchThat, false, true);
			} else SynErr(188);
			Expect(28);
			endTok = t; 
		} else if (la.kind == 21) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(189);
		if (suchThat != null) {
		 s = new AssignSuchThatStmt(x, endTok, lhss, suchThat, suchThatAssume, null);
		} else {
		 if (lhss.Count == 0 && rhss.Count == 0) {
		   s = new BlockStmt(x, endTok, new List<Statement>()); // error, give empty statement
		 } else {
		   s = new UpdateStmt(x, endTok, lhss, rhss);
		 }
		}
		
	}

	void VarDeclStatement(out Statement/*!*/ s) {
		IToken x = null, assignTok = null;  bool isGhost = false;
		LocalVariable d;
		AssignmentRhs r;
		List<LocalVariable> lhss = new List<LocalVariable>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		IToken suchThatAssume = null;
		Expression suchThat = null;
		Attributes attrs = null;
		IToken endTok;
		s = dummyStmt;
		
		if (la.kind == 62) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(82);
		if (!isGhost) { x = t; } 
		if (la.kind == 1 || la.kind == 46) {
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			LocalIdentTypeOptional(out d, isGhost);
			lhss.Add(d); d.Attributes = attrs; attrs = null; 
			while (la.kind == 22) {
				Get();
				while (la.kind == 46) {
					Attribute(ref attrs);
				}
				LocalIdentTypeOptional(out d, isGhost);
				lhss.Add(d); d.Attributes = attrs; attrs = null; 
			}
			if (la.kind == 25 || la.kind == 46 || la.kind == 99) {
				if (la.kind == 99) {
					Get();
					assignTok = t; 
					Rhs(out r);
					rhss.Add(r); 
					while (la.kind == 22) {
						Get();
						Rhs(out r);
						rhss.Add(r); 
					}
				} else {
					while (la.kind == 46) {
						Attribute(ref attrs);
					}
					Expect(25);
					assignTok = t; 
					if (la.kind == _assume) {
						Expect(31);
						suchThatAssume = t; 
					}
					Expression(out suchThat, false, true);
				}
			}
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(190); Get();}
			Expect(28);
			endTok = t; 
			ConcreteUpdateStatement update;
			if (suchThat != null) {
			 var ies = new List<Expression>();
			 foreach (var lhs in lhss) {
			   ies.Add(new IdentifierExpr(lhs.Tok, lhs.Name));
			 }
			 update = new AssignSuchThatStmt(assignTok, endTok, ies, suchThat, suchThatAssume, attrs);
			} else if (rhss.Count == 0) {
			 update = null;
			} else {
			 var ies = new List<Expression>();
			 foreach (var lhs in lhss) {
			   ies.Add(new AutoGhostIdentifierExpr(lhs.Tok, lhs.Name));
			 }
			 update = new UpdateStmt(assignTok, endTok, ies, rhss);
			}
			s = new VarDeclStmt(x, endTok, lhss, update);
			
		} else if (la.kind == 50) {
			Get();
			var letLHSs = new List<CasePattern>();
			var letRHSs = new List<Expression>();
			List<CasePattern> arguments = new List<CasePattern>();
			CasePattern pat;
			Expression e = dummyExpr;
			IToken id = t;
			
			if (la.kind == 1 || la.kind == 50) {
				CasePattern(out pat);
				arguments.Add(pat); 
				while (la.kind == 22) {
					Get();
					CasePattern(out pat);
					arguments.Add(pat); 
				}
			}
			Expect(51);
			theBuiltIns.TupleType(id, arguments.Count, true); // make sure the tuple type exists
			string ctor = BuiltIns.TupleTypeCtorName;  //use the TupleTypeCtors
			pat = new CasePattern(id, ctor, arguments); 
			if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
			letLHSs.Add(pat);
			
			if (la.kind == 99) {
				Get();
			} else if (la.kind == 25 || la.kind == 46) {
				while (la.kind == 46) {
					Attribute(ref attrs);
				}
				Expect(25);
				SemErr(pat.tok, "LHS of assign-such-that expression must be variables, not general patterns"); 
			} else SynErr(191);
			Expression(out e, false, true);
			letRHSs.Add(e); 
			Expect(28);
			s = new LetStmt(e.tok, e.tok, letLHSs, letRHSs); 
		} else SynErr(192);
	}

	void IfStmt(out Statement/*!*/ ifStmt) {
		Contract.Ensures(Contract.ValueAtReturn(out ifStmt) != null); IToken/*!*/ x;
		Expression guard = null;  IToken guardEllipsis = null;  bool isExistentialGuard = false;
		BlockStmt/*!*/ thn;
		BlockStmt/*!*/ bs;
		Statement/*!*/ s;
		Statement els = null;
		IToken bodyStart, bodyEnd, endTok;
		List<GuardedAlternative> alternatives;
		ifStmt = dummyStmt;  // to please the compiler
		
		Expect(102);
		x = t; 
		if (IsAlternative()) {
			AlternativeBlock(true, out alternatives, out endTok);
			ifStmt = new AlternativeStmt(x, endTok, alternatives); 
		} else if (StartOf(22)) {
			if (IsExistentialGuard()) {
				ExistentialGuard(out guard, true);
				isExistentialGuard = true; 
			} else if (StartOf(23)) {
				Guard(out guard);
			} else {
				Get();
				guardEllipsis = t; 
			}
			BlockStmt(out thn, out bodyStart, out bodyEnd);
			endTok = thn.EndTok; 
			if (la.kind == 35) {
				Get();
				if (la.kind == 102) {
					IfStmt(out s);
					els = s; endTok = s.EndTok; 
				} else if (la.kind == 46) {
					BlockStmt(out bs, out bodyStart, out bodyEnd);
					els = bs; endTok = bs.EndTok; 
				} else SynErr(193);
			}
			if (guardEllipsis != null) {
			 ifStmt = new SkeletonStatement(new IfStmt(x, endTok, isExistentialGuard, guard, thn, els), guardEllipsis, null);
			} else {
			 ifStmt = new IfStmt(x, endTok, isExistentialGuard, guard, thn, els);
			}
			
		} else SynErr(194);
	}

	void WhileStmt(out Statement stmt) {
		Contract.Ensures(Contract.ValueAtReturn(out stmt) != null); IToken x;
		Expression guard = null;  IToken guardEllipsis = null;
		
		List<MaybeFreeExpression> invariants = new List<MaybeFreeExpression>();
		List<Expression> decreases = new List<Expression>();
		Attributes decAttrs = null;
		Attributes modAttrs = null;
		List<FrameExpression> mod = null;
		
		BlockStmt body = null;  IToken bodyEllipsis = null;
		IToken bodyStart = null, bodyEnd = null, endTok = Token.NoToken;
		List<GuardedAlternative> alternatives;
		stmt = dummyStmt;  // to please the compiler
		bool isDirtyLoop = true;
		
		Expect(103);
		x = t; 
		if (IsLoopSpec() || IsAlternative()) {
			while (StartOf(24)) {
				LoopSpec(invariants, decreases, ref mod, ref decAttrs, ref modAttrs);
			}
			AlternativeBlock(false, out alternatives, out endTok);
			stmt = new AlternativeLoopStmt(x, endTok, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(mod, modAttrs), alternatives); 
		} else if (StartOf(22)) {
			if (StartOf(23)) {
				Guard(out guard);
				Contract.Assume(guard == null || cce.Owner.None(guard)); 
			} else {
				Get();
				guardEllipsis = t; 
			}
			while (StartOf(24)) {
				LoopSpec(invariants, decreases, ref mod, ref decAttrs, ref modAttrs);
			}
			if (la.kind == _lbrace) {
				BlockStmt(out body, out bodyStart, out bodyEnd);
				endTok = body.EndTok; isDirtyLoop = false; 
			} else if (la.kind == _ellipsis) {
				Expect(59);
				bodyEllipsis = t; endTok = t; isDirtyLoop = false; 
			} else if (StartOf(25)) {
			} else SynErr(195);
			if (guardEllipsis != null || bodyEllipsis != null) {
			 if (mod != null) {
			   SemErr(mod[0].E.tok, "'modifies' clauses are not allowed on refining loops");
			 }
			 if (body == null && !isDirtyLoop) {
			   body = new BlockStmt(x, endTok, new List<Statement>());
			 }
			 stmt = new WhileStmt(x, endTok, guard, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(null, null), body);
			 stmt = new SkeletonStatement(stmt, guardEllipsis, bodyEllipsis);
			} else {
			 // The following statement protects against crashes in case of parsing errors
			 if (body == null && !isDirtyLoop) {
			   body = new BlockStmt(x, endTok, new List<Statement>());
			 }
			 stmt = new WhileStmt(x, endTok, guard, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(mod, modAttrs), body);
			}
			
		} else SynErr(196);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(104);
		x = t; 
		Expression(out e, true, true);
		if (la.kind == _lbrace) {
			Expect(46);
			usesOptionalBrace = true; 
			while (la.kind == 33) {
				CaseStatement(out c);
				cases.Add(c); 
			}
			Expect(47);
		} else if (StartOf(25)) {
			while (la.kind == _case) {
				CaseStatement(out c);
				cases.Add(c); 
			}
		} else SynErr(197);
		s = new MatchStmt(x, t, e, cases, usesOptionalBrace); 
	}

	void ForallStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		IToken/*!*/ x = Token.NoToken;
		List<BoundVar> bvars = null;
		Attributes attrs = null;
		Expression range = null;
		var ens = new List<MaybeFreeExpression/*!*/>();
		bool isFree;
		Expression/*!*/ e;
		BlockStmt block = null;
		IToken bodyStart, bodyEnd;
		IToken tok = Token.NoToken;
		
		if (la.kind == 107) {
			Get();
			x = t; tok = x; 
		} else if (la.kind == 108) {
			Get();
			x = t;
			errors.Warning(t, "the 'parallel' keyword has been deprecated; the comprehension statement now uses the keyword 'forall' (and the parentheses around the bound variables are now optional)");
			
		} else SynErr(198);
		if (la.kind == _openparen) {
			Expect(50);
			if (la.kind == 1) {
				QuantifierDomain(out bvars, out attrs, out range);
			}
			Expect(51);
		} else if (StartOf(26)) {
			if (la.kind == _ident) {
				QuantifierDomain(out bvars, out attrs, out range);
			}
		} else SynErr(199);
		if (bvars == null) { bvars = new List<BoundVar>(); }
		if (range == null) { range = new LiteralExpr(x, true); }
		
		while (la.kind == 92 || la.kind == 93) {
			isFree = false; 
			if (la.kind == 92) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			Expect(93);
			Expression(out e, false, true);
			ens.Add(new MaybeFreeExpression(e, isFree)); 
			OldSemi();
			tok = t; 
		}
		if (la.kind == _lbrace) {
			BlockStmt(out block, out bodyStart, out bodyEnd);
		}
		if (DafnyOptions.O.DisallowSoundnessCheating && block == null && 0 < ens.Count) {
		  SemErr(t, "a forall statement with an ensures clause must have a body");
		}
		
		if (block != null) {
		  tok = block.EndTok;
		}
		s = new ForallStmt(x, tok, bvars, attrs, range, ens, block);
		
	}

	void CalcStmt(out Statement s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;
		Attributes attrs = null;
		CalcStmt.CalcOp op, calcOp = Microsoft.Dafny.CalcStmt.DefaultOp, resOp = Microsoft.Dafny.CalcStmt.DefaultOp;
		var lines = new List<Expression>();
		var hints = new List<BlockStmt>();
		CalcStmt.CalcOp stepOp;
		var stepOps = new List<CalcStmt.CalcOp>();
		CalcStmt.CalcOp maybeOp;
		Expression e;
		IToken opTok;
		IToken danglingOperator = null;
		
		Expect(32);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(27)) {
			CalcOp(out opTok, out calcOp);
			maybeOp = calcOp.ResultOp(calcOp); // guard against non-transitive calcOp (like !=)
			if (maybeOp == null) {
			 SemErr(opTok, "the main operator of a calculation must be transitive");
			}
			resOp = calcOp;
			
		}
		Expect(46);
		while (StartOf(9)) {
			Expression(out e, false, true);
			lines.Add(e); stepOp = calcOp; danglingOperator = null; 
			Expect(28);
			if (StartOf(27)) {
				CalcOp(out opTok, out op);
				maybeOp = resOp.ResultOp(op);
				if (maybeOp == null) {
				 SemErr(opTok, "this operator cannot continue this calculation");
				} else {
				 stepOp = op;
				 resOp = maybeOp;
				 danglingOperator = opTok;
				}
				
			}
			stepOps.Add(stepOp); 
			var subhints = new List<Statement>();
			IToken hintStart = la;  IToken hintEnd = hintStart;
			IToken t0, t1;
			BlockStmt subBlock; Statement subCalc;
			
			while (la.kind == _lbrace || la.kind == _calc) {
				if (la.kind == 46) {
					BlockStmt(out subBlock, out t0, out t1);
					hintEnd = subBlock.EndTok; subhints.Add(subBlock); 
				} else if (la.kind == 32) {
					CalcStmt(out subCalc);
					hintEnd = subCalc.EndTok; subhints.Add(subCalc); 
				} else SynErr(200);
			}
			var h = new BlockStmt(hintStart, hintEnd, subhints); // if the hint is empty, hintStart is the first token of the next line, but it doesn't matter because the block statement is just used as a container
			hints.Add(h);
			if (h.Body.Count != 0) { danglingOperator = null; }
			
		}
		Expect(47);
		if (danglingOperator != null) {
		 SemErr(danglingOperator, "a calculation cannot end with an operator");
		}
		if (lines.Count > 0) {
		 // Repeat the last line to create a dummy line for the dangling hint
		 lines.Add(lines[lines.Count - 1]);
		}
		s = new CalcStmt(x, t, calcOp, lines, hints, stepOps, resOp, attrs);
		
	}

	void ModifyStmt(out Statement s) {
		IToken tok;  IToken endTok = Token.NoToken;
		Attributes attrs = null;
		FrameExpression fe;  var mod = new List<FrameExpression>();
		BlockStmt body = null;  IToken bodyStart;
		IToken ellipsisToken = null;
		
		Expect(109);
		tok = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(20)) {
			FrameExpression(out fe, false, true);
			mod.Add(fe); 
			while (la.kind == 22) {
				Get();
				FrameExpression(out fe, false, true);
				mod.Add(fe); 
			}
		} else if (la.kind == 59) {
			Get();
			ellipsisToken = t; 
		} else SynErr(201);
		if (la.kind == 46) {
			BlockStmt(out body, out bodyStart, out endTok);
		} else if (la.kind == 28) {
			while (!(la.kind == 0 || la.kind == 28)) {SynErr(202); Get();}
			Get();
			endTok = t; 
		} else SynErr(203);
		s = new ModifyStmt(tok, endTok, mod, attrs, body);
		if (ellipsisToken != null) {
		 s = new SkeletonStatement(s, ellipsisToken, null);
		}
		
	}

	void ReturnStmt(out Statement/*!*/ s) {
		IToken returnTok = null;
		List<AssignmentRhs> rhss = null;
		AssignmentRhs r;
		bool isYield = false;
		
		if (la.kind == 100) {
			Get();
			returnTok = t; 
		} else if (la.kind == 94) {
			Get();
			returnTok = t; isYield = true; 
		} else SynErr(204);
		if (StartOf(28)) {
			Rhs(out r);
			rhss = new List<AssignmentRhs>(); rhss.Add(r); 
			while (la.kind == 22) {
				Get();
				Rhs(out r);
				rhss.Add(r); 
			}
		}
		Expect(28);
		if (isYield) {
		 s = new YieldStmt(returnTok, t, rhss);
		} else {
		 s = new ReturnStmt(returnTok, t, rhss);
		}
		
	}

	void SkeletonStmt(out Statement s) {
		List<IToken> names = null;
		List<Expression> exprs = null;
		IToken tok, dotdotdot, whereTok;
		Expression e; 
		Expect(59);
		dotdotdot = t; 
		if (la.kind == 98) {
			Get();
			names = new List<IToken>(); exprs = new List<Expression>(); whereTok = t;
			Ident(out tok);
			names.Add(tok); 
			while (la.kind == 22) {
				Get();
				Ident(out tok);
				names.Add(tok); 
			}
			Expect(99);
			Expression(out e, false, true);
			exprs.Add(e); 
			while (la.kind == 22) {
				Get();
				Expression(out e, false, true);
				exprs.Add(e); 
			}
			if (exprs.Count != names.Count) {
			 SemErr(whereTok, exprs.Count < names.Count ? "not enough expressions" : "too many expressions");
			 names = null; exprs = null;
			}
			
		}
		Expect(28);
		s = new SkeletonStatement(dotdotdot, t, names, exprs); 
	}

	void Rhs(out AssignmentRhs r) {
		Contract.Ensures(Contract.ValueAtReturn<AssignmentRhs>(out r) != null);
		IToken/*!*/ x, newToken;  Expression/*!*/ e;
		Type ty = null;
		List<Expression> ee = null;
		List<Expression> args = null;
		r = dummyRhs;  // to please compiler
		Attributes attrs = null;
		
		if (la.kind == 101) {
			Get();
			newToken = t; 
			TypeAndToken(out x, out ty);
			if (la.kind == 48 || la.kind == 50) {
				if (la.kind == 48) {
					Get();
					ee = new List<Expression>(); 
					Expressions(ee);
					Expect(49);
					var tmp = theBuiltIns.ArrayType(ee.Count, new IntType(), true);
					
				} else {
					x = null; args = new List<Expression/*!*/>(); 
					Get();
					if (StartOf(9)) {
						Expressions(args);
					}
					Expect(51);
				}
			}
			if (ee != null) {
			 r = new TypeRhs(newToken, ty, ee);
			} else if (args != null) {
			 r = new TypeRhs(newToken, ty, args, false);
			} else {
			 r = new TypeRhs(newToken, ty);
			}
			
		} else if (la.kind == 57) {
			Get();
			r = new HavocRhs(t); 
		} else if (StartOf(9)) {
			Expression(out e, false, true);
			r = new ExprRhs(e); 
		} else SynErr(205);
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		r.Attributes = attrs; 
	}

	void Lhs(out Expression e) {
		e = dummyExpr;  // the assignment is to please the compiler, the dummy value to satisfy contracts in the event of a parse error
		
		if (la.kind == 1) {
			NameSegment(out e);
			while (la.kind == 27 || la.kind == 48 || la.kind == 50) {
				Suffix(ref e);
			}
		} else if (StartOf(29)) {
			ConstAtomExpression(out e, false, false);
			Suffix(ref e);
			while (la.kind == 27 || la.kind == 48 || la.kind == 50) {
				Suffix(ref e);
			}
		} else SynErr(206);
	}

	void Expressions(List<Expression> args) {
		Expression e; 
		Expression(out e, true, true);
		args.Add(e); 
		while (la.kind == 22) {
			Get();
			Expression(out e, true, true);
			args.Add(e); 
		}
	}

	void CasePattern(out CasePattern pat) {
		IToken id;  List<CasePattern> arguments;
		BoundVar bv;
		pat = null;
		
		if (IsIdentParen()) {
			Ident(out id);
			Expect(50);
			arguments = new List<CasePattern>(); 
			if (la.kind == 1 || la.kind == 50) {
				CasePattern(out pat);
				arguments.Add(pat); 
				while (la.kind == 22) {
					Get();
					CasePattern(out pat);
					arguments.Add(pat); 
				}
			}
			Expect(51);
			pat = new CasePattern(id, id.val, arguments); 
		} else if (la.kind == 50) {
			Get();
			id = t;                                                           
			arguments = new List<CasePattern>(); 
			
			if (la.kind == 1 || la.kind == 50) {
				CasePattern(out pat);
				arguments.Add(pat); 
				while (la.kind == 22) {
					Get();
					CasePattern(out pat);
					arguments.Add(pat); 
				}
			}
			Expect(51);
			theBuiltIns.TupleType(id, arguments.Count, true); // make sure the tuple type exists
			string ctor = BuiltIns.TupleTypeCtorName;  //use the TupleTypeCtors
			pat = new CasePattern(id, ctor, arguments); 
			
		} else if (la.kind == 1) {
			IdentTypeOptional(out bv);
			pat = new CasePattern(bv.tok, bv);
			
		} else SynErr(207);
		if (pat == null) {
		 pat = new CasePattern(t, "_ParseError", new List<CasePattern>());
		}
		
	}

	void AlternativeBlock(bool allowExistentialGuards, out List<GuardedAlternative> alternatives, out IToken endTok) {
		alternatives = new List<GuardedAlternative>();
		IToken x;
		Expression e; bool isExistentialGuard;
		List<Statement> body;
		
		Expect(46);
		while (la.kind == 33) {
			Get();
			x = t; isExistentialGuard = false; e = dummyExpr; 
			if (allowExistentialGuards && IsExistentialGuard()) {
				ExistentialGuard(out e, false );
				isExistentialGuard = true; 
			} else if (StartOf(9)) {
				Expression(out e, true, false);
			} else SynErr(208);
			Expect(29);
			body = new List<Statement>(); 
			while (StartOf(17)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, isExistentialGuard, e, body)); 
		}
		Expect(47);
		endTok = t; 
	}

	void ExistentialGuard(out Expression e, bool allowLambda) {
		var bvars = new List<BoundVar>();
		BoundVar bv;  IToken x;
		Attributes attrs = null;
		Expression body;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); x = bv.tok; 
		while (la.kind == 22) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		Expect(25);
		Expression(out body, true, allowLambda);
		e = new ExistsExpr(x, bvars, null, body, attrs); 
	}

	void Guard(out Expression e) {
		Expression/*!*/ ee;  e = null; 
		if (la.kind == 57) {
			Get();
			e = null; 
		} else if (IsParenStar()) {
			Expect(50);
			Expect(57);
			Expect(51);
			e = null; 
		} else if (StartOf(9)) {
			Expression(out ee, true, true);
			e = ee; 
		} else SynErr(209);
	}

	void LoopSpec(List<MaybeFreeExpression> invariants, List<Expression> decreases, ref List<FrameExpression> mod, ref Attributes decAttrs, ref Attributes modAttrs) {
		Expression e; FrameExpression fe;
		bool isFree = false; Attributes attrs = null;
		
		if (la.kind == 37 || la.kind == 92) {
			while (!(la.kind == 0 || la.kind == 37 || la.kind == 92)) {SynErr(210); Get();}
			if (la.kind == 92) {
				Get();
				isFree = true; errors.Warning(t, "the 'free' keyword is soon to be deprecated"); 
			}
			Expect(37);
			while (IsAttribute()) {
				Attribute(ref attrs);
			}
			Expression(out e, false, true);
			invariants.Add(new MaybeFreeExpression(e, isFree, attrs)); 
			OldSemi();
		} else if (la.kind == 36) {
			while (!(la.kind == 0 || la.kind == 36)) {SynErr(211); Get();}
			Get();
			while (IsAttribute()) {
				Attribute(ref decAttrs);
			}
			DecreasesList(decreases, true, true);
			OldSemi();
		} else if (la.kind == 43) {
			while (!(la.kind == 0 || la.kind == 43)) {SynErr(212); Get();}
			Get();
			mod = mod ?? new List<FrameExpression>(); 
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, true);
			mod.Add(fe); 
			while (la.kind == 22) {
				Get();
				FrameExpression(out fe, false, true);
				mod.Add(fe); 
			}
			OldSemi();
		} else SynErr(213);
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id;
		List<CasePattern/*!*/> arguments = new List<CasePattern/*!*/>();
		CasePattern/*!*/ pat;
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		string/*!*/ name = "";
		
		Expect(33);
		x = t; 
		if (la.kind == 1) {
			Ident(out id);
			name = id.val; 
			if (la.kind == 50) {
				Get();
				if (la.kind == 1 || la.kind == 50) {
					CasePattern(out pat);
					arguments.Add(pat); 
					while (la.kind == 22) {
						Get();
						CasePattern(out pat);
						arguments.Add(pat); 
					}
				}
				Expect(51);
			}
		} else if (la.kind == 50) {
			Get();
			CasePattern(out pat);
			arguments.Add(pat); 
			while (la.kind == 22) {
				Get();
				CasePattern(out pat);
				arguments.Add(pat); 
			}
			Expect(51);
		} else SynErr(214);
		Expect(29);
		while (!(StartOf(30))) {SynErr(215); Get();}
		while (IsNotEndOfCase()) {
			Stmt(body);
			while (!(StartOf(30))) {SynErr(216); Get();}
		}
		c = new MatchCaseStmt(x, name, arguments, body); 
	}

	void QuantifierDomain(out List<BoundVar> bvars, out Attributes attrs, out Expression range) {
		bvars = new List<BoundVar>();
		BoundVar/*!*/ bv;
		attrs = null;
		range = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 22) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (la.kind == _verticalbar) {
			Expect(23);
			Expression(out range, true, true);
		}
	}

	void CalcOp(out IToken x, out CalcStmt.CalcOp/*!*/ op) {
		var binOp = BinaryExpr.Opcode.Eq; // Returns Eq if parsing fails because it is compatible with any other operator
		Expression k = null;
		x = null;
		
		switch (la.kind) {
		case 54: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Eq; 
			if (la.kind == 110) {
				Get();
				Expect(48);
				Expression(out k, true, true);
				Expect(49);
			}
			break;
		}
		case 52: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 53: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 111: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 112: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 55: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 56: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 113: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 114: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 115: case 116: {
			EquivOp();
			x = t;  binOp = BinaryExpr.Opcode.Iff; 
			break;
		}
		case 117: case 118: {
			ImpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Imp; 
			break;
		}
		case 119: case 120: {
			ExpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Exp; 
			break;
		}
		default: SynErr(217); break;
		}
		if (k == null) {
		 op = new Microsoft.Dafny.CalcStmt.BinaryCalcOp(binOp);
		} else {
		 op = new Microsoft.Dafny.CalcStmt.TernaryCalcOp(k);
		}
		
	}

	void EquivOp() {
		if (la.kind == 115) {
			Get();
		} else if (la.kind == 116) {
			Get();
		} else SynErr(218);
	}

	void ImpliesOp() {
		if (la.kind == 117) {
			Get();
		} else if (la.kind == 118) {
			Get();
		} else SynErr(219);
	}

	void ExpliesOp() {
		if (la.kind == 119) {
			Get();
		} else if (la.kind == 120) {
			Get();
		} else SynErr(220);
	}

	void AndOp() {
		if (la.kind == 121) {
			Get();
		} else if (la.kind == 122) {
			Get();
		} else SynErr(221);
	}

	void OrOp() {
		if (la.kind == 123) {
			Get();
		} else if (la.kind == 124) {
			Get();
		} else SynErr(222);
	}

	void NegOp() {
		if (la.kind == 125) {
			Get();
		} else if (la.kind == 126) {
			Get();
		} else SynErr(223);
	}

	void Forall() {
		if (la.kind == 107) {
			Get();
		} else if (la.kind == 127) {
			Get();
		} else SynErr(224);
	}

	void Exists() {
		if (la.kind == 128) {
			Get();
		} else if (la.kind == 129) {
			Get();
		} else SynErr(225);
	}

	void QSep() {
		if (la.kind == 24) {
			Get();
		} else if (la.kind == 26) {
			Get();
		} else SynErr(226);
	}

	void EquivExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		ImpliesExpliesExpression(out e0, allowSemi, allowLambda);
		while (IsEquivOp()) {
			EquivOp();
			x = t; 
			ImpliesExpliesExpression(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Iff, e0, e1); 
		}
	}

	void ImpliesExpliesExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0, allowSemi, allowLambda);
		if (IsImpliesOp() || IsExpliesOp()) {
			if (la.kind == 117 || la.kind == 118) {
				ImpliesOp();
				x = t; 
				ImpliesExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
			} else if (la.kind == 119 || la.kind == 120) {
				ExpliesOp();
				x = t; 
				LogicalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e1, e0); 
				while (IsExpliesOp()) {
					ExpliesOp();
					x = t; 
					LogicalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e1, e0); 
					
				}
			} else SynErr(227);
		}
	}

	void LogicalExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0, allowSemi, allowLambda);
		if (IsAndOp() || IsOrOp()) {
			if (la.kind == 121 || la.kind == 122) {
				AndOp();
				x = t; 
				RelationalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				while (IsAndOp()) {
					AndOp();
					x = t; 
					RelationalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				}
			} else if (la.kind == 123 || la.kind == 124) {
				OrOp();
				x = t; 
				RelationalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				while (IsOrOp()) {
					OrOp();
					x = t; 
					RelationalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				}
			} else SynErr(228);
		}
	}

	void ImpliesExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0, allowSemi, allowLambda);
		if (IsImpliesOp()) {
			ImpliesOp();
			x = t; 
			ImpliesExpression(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
		}
	}

	void RelationalExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken x, firstOpTok = null;  Expression e0, e1, acc = null;  BinaryExpr.Opcode op;
		List<Expression> chain = null;
		List<BinaryExpr.Opcode> ops = null;
		List<Expression/*?*/> prefixLimits = null;
		Expression k;
		int kind = 0;  // 0 ("uncommitted") indicates chain of ==, possibly with one !=
		              // 1 ("ascending")   indicates chain of ==, <, <=, possibly with one !=
		              // 2 ("descending")  indicates chain of ==, >, >=, possibly with one !=
		              // 3 ("illegal")     indicates illegal chain
		              // 4 ("disjoint")    indicates chain of disjoint set operators
		bool hasSeenNeq = false;
		
		Term(out e0, allowSemi, allowLambda);
		e = e0; 
		if (IsRelOp()) {
			RelOp(out x, out op, out k);
			firstOpTok = x; 
			Term(out e1, allowSemi, allowLambda);
			if (k == null) {
			 e = new BinaryExpr(x, op, e0, e1);
			 if (op == BinaryExpr.Opcode.Disjoint)
			   acc = new BinaryExpr(x, BinaryExpr.Opcode.Add, e0, e1); // accumulate first two operands.
			} else {
			 Contract.Assert(op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq);
			 e = new TernaryExpr(x, op == BinaryExpr.Opcode.Eq ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp, k, e0, e1);
			}
			
			while (IsRelOp()) {
				if (chain == null) {
				 chain = new List<Expression>();
				 ops = new List<BinaryExpr.Opcode>();
				 prefixLimits = new List<Expression>();
				 chain.Add(e0);  ops.Add(op);  prefixLimits.Add(k);  chain.Add(e1);
				 switch (op) {
				   case BinaryExpr.Opcode.Eq:
				     kind = 0;  break;
				   case BinaryExpr.Opcode.Neq:
				     kind = 0;  hasSeenNeq = true;  break;
				   case BinaryExpr.Opcode.Lt:
				   case BinaryExpr.Opcode.Le:
				     kind = 1;  break;
				   case BinaryExpr.Opcode.Gt:
				   case BinaryExpr.Opcode.Ge:
				     kind = 2;  break;
				   case BinaryExpr.Opcode.Disjoint:
				     kind = 4;  break;
				   default:
				     kind = 3;  break;
				 }
				}
				e0 = e1;
				
				RelOp(out x, out op, out k);
				switch (op) {
				 case BinaryExpr.Opcode.Eq:
				   if (kind != 0 && kind != 1 && kind != 2) { SemErr(x, "chaining not allowed from the previous operator"); }
				   break;
				 case BinaryExpr.Opcode.Neq:
				   if (hasSeenNeq) { SemErr(x, "a chain cannot have more than one != operator"); }
				   if (kind != 0 && kind != 1 && kind != 2) { SemErr(x, "this operator cannot continue this chain"); }
				   hasSeenNeq = true;  break;
				 case BinaryExpr.Opcode.Lt:
				 case BinaryExpr.Opcode.Le:
				   if (kind == 0) { kind = 1; }
				   else if (kind != 1) { SemErr(x, "this operator chain cannot continue with an ascending operator"); }
				   break;
				 case BinaryExpr.Opcode.Gt:
				 case BinaryExpr.Opcode.Ge:
				   if (kind == 0) { kind = 2; }
				   else if (kind != 2) { SemErr(x, "this operator chain cannot continue with a descending operator"); }
				   break;
				 case BinaryExpr.Opcode.Disjoint:
				   if (kind != 4) { SemErr(x, "can only chain disjoint (!!) with itself."); kind = 3; }
				   break;
				 default:
				   SemErr(x, "this operator cannot be part of a chain");
				   kind = 3;  break;
				}
				
				Term(out e1, allowSemi, allowLambda);
				ops.Add(op); prefixLimits.Add(k); chain.Add(e1);
				if (k != null) {
				 Contract.Assert(op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq);
				 e = new TernaryExpr(x, op == BinaryExpr.Opcode.Eq ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp, k, e0, e1);
				} else if (op == BinaryExpr.Opcode.Disjoint && acc != null) {  // the second conjunct always holds for legal programs
				 e = new BinaryExpr(x, BinaryExpr.Opcode.And, e, new BinaryExpr(x, op, acc, e1));
				 acc = new BinaryExpr(x, BinaryExpr.Opcode.Add, acc, e1); //e0 has already been added.
				} else {
				 e = new BinaryExpr(x, BinaryExpr.Opcode.And, e, new BinaryExpr(x, op, e0, e1));
				}
				
			}
		}
		if (chain != null) {
		 e = new ChainingExpression(firstOpTok, chain, ops, prefixLimits, e);
		}
		
	}

	void Term(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		Factor(out e0, allowSemi, allowLambda);
		while (IsAddOp()) {
			AddOp(out x, out op);
			Factor(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryExpr.Opcode op, out Expression k) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/;
		IToken y;
		k = null;
		
		switch (la.kind) {
		case 54: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			if (la.kind == 110) {
				Get();
				Expect(48);
				Expression(out k, true, true);
				Expect(49);
			}
			break;
		}
		case 52: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 53: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 111: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 112: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 55: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			if (la.kind == 110) {
				Get();
				Expect(48);
				Expression(out k, true, true);
				Expect(49);
			}
			break;
		}
		case 130: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 58: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 125: {
			Get();
			x = t;  y = Token.NoToken; 
			if (la.val == "!") {
				Expect(125);
				y = t; 
			}
			if (y == Token.NoToken) {
			 SemErr(x, "invalid RelOp");
			} else if (y.pos != x.pos + 1) {
			 SemErr(x, "invalid RelOp (perhaps you intended \"!!\" with no intervening whitespace?)");
			} else {
			 x.val = "!!";
			 op = BinaryExpr.Opcode.Disjoint;
			}
			
			break;
		}
		case 56: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 113: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 114: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(229); break;
		}
	}

	void Factor(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0, allowSemi, allowLambda);
		while (IsMulOp()) {
			MulOp(out x, out op);
			UnaryExpression(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 131) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 132) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(230);
	}

	void UnaryExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		if (la.kind == 132) {
			Get();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new NegationExpression(x, e); 
		} else if (la.kind == 125 || la.kind == 126) {
			NegOp();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Not, e); 
		} else if (IsMapDisplay()) {
			Expect(17);
			x = t; 
			MapDisplayExpr(x, true, out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (IsIMapDisplay()) {
			Expect(18);
			x = t; 
			MapDisplayExpr(x, false, out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (IsISetDisplay()) {
			Expect(14);
			x = t; 
			ISetDisplayExpr(x, false, out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (IsLambda(allowLambda)) {
			LambdaExpression(out e, allowSemi);
		} else if (StartOf(31)) {
			EndlessExpression(out e, allowSemi, allowLambda);
		} else if (la.kind == 1) {
			NameSegment(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (la.kind == 46 || la.kind == 48) {
			DisplayExpr(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (la.kind == 15) {
			MultiSetExpr(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (StartOf(29)) {
			ConstAtomExpression(out e, allowSemi, allowLambda);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else SynErr(231);
	}

	void MulOp(out IToken x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 57) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 133) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 134) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(232);
	}

	void MapDisplayExpr(IToken/*!*/ mapToken, bool finite, out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		List<ExpressionPair/*!*/>/*!*/ elements= new List<ExpressionPair/*!*/>() ;
		e = dummyExpr;
		
		Expect(48);
		if (StartOf(9)) {
			MapLiteralExpressions(out elements);
		}
		e = new MapDisplayExpr(mapToken, finite, elements);
		Expect(49);
	}

	void Suffix(ref Expression e) {
		Contract.Requires(e != null); Contract.Ensures(e!=null);
		IToken id, x;
		Expression e0 = null;  Expression e1 = null;  Expression ee;  bool anyDots = false;
		List<Expression> multipleLengths = null; bool takeRest = false; // takeRest is relevant only if multipleLengths is non-null
		List<Expression> multipleIndices = null;
		List<Tuple<IToken, string, Expression>> updates;
		Expression v;
		
		if (la.kind == 27) {
			Get();
			if (la.kind == 50) {
				Get();
				x = t; updates = new List<Tuple<IToken, string, Expression>>(); 
				MemberBindingUpdate(out id, out v);
				updates.Add(Tuple.Create(id, id.val, v)); 
				while (la.kind == 22) {
					Get();
					MemberBindingUpdate(out id, out v);
					updates.Add(Tuple.Create(id, id.val, v)); 
				}
				Expect(51);
				e = new DatatypeUpdateExpr(x, e, updates); 
			} else if (StartOf(32)) {
				DotSuffix(out id, out x);
				if (x != null) {
				 // process id as a Suffix in its own right
				 e = new ExprDotName(id, e, id.val, null);
				 id = x;  // move to the next Suffix
				}
				IToken openParen = null;  List<Type> typeArgs = null;  List<Expression> args = null;
				
				if (IsGenericInstantiation()) {
					typeArgs = new List<Type>(); 
					GenericInstantiation(typeArgs);
				} else if (la.kind == 110) {
					HashCall(id, out openParen, out typeArgs, out args);
				} else if (StartOf(33)) {
				} else SynErr(233);
				e = new ExprDotName(id, e, id.val, typeArgs);
				if (openParen != null) {
				 e = new ApplySuffix(openParen, e, args);
				}
				
			} else SynErr(234);
		} else if (la.kind == 48) {
			Get();
			x = t; 
			if (StartOf(9)) {
				Expression(out ee, true, true);
				e0 = ee; 
				if (la.kind == 141) {
					Get();
					anyDots = true; 
					if (StartOf(9)) {
						Expression(out ee, true, true);
						e1 = ee; 
					}
				} else if (la.kind == 99) {
					Get();
					Expression(out ee, true, true);
					e1 = ee; 
				} else if (la.kind == 21) {
					Get();
					multipleLengths = new List<Expression>();
					multipleLengths.Add(e0);  // account for the Expression read before the colon
					takeRest = true;
					
					if (StartOf(9)) {
						Expression(out ee, true, true);
						multipleLengths.Add(ee); takeRest = false; 
						while (IsNonFinalColon()) {
							Expect(21);
							Expression(out ee, true, true);
							multipleLengths.Add(ee); 
						}
						if (la.kind == 21) {
							Get();
							takeRest = true; 
						}
					}
				} else if (la.kind == 22 || la.kind == 49) {
					while (la.kind == 22) {
						Get();
						Expression(out ee, true, true);
						if (multipleIndices == null) {
						 multipleIndices = new List<Expression>();
						 multipleIndices.Add(e0);
						}
						multipleIndices.Add(ee);
						
					}
				} else SynErr(235);
			} else if (la.kind == 141) {
				Get();
				anyDots = true; 
				if (StartOf(9)) {
					Expression(out ee, true, true);
					e1 = ee; 
				}
			} else SynErr(236);
			if (multipleIndices != null) {
			 e = new MultiSelectExpr(x, e, multipleIndices);
			 // make sure an array class with this dimensionality exists
			 var tmp = theBuiltIns.ArrayType(multipleIndices.Count, new IntType(), true);
			} else {
			 if (!anyDots && e0 == null) {
			   /* a parsing error occurred */
			   e0 = dummyExpr;
			 }
			 Contract.Assert(anyDots || e0 != null);
			 if (anyDots) {
			   //Contract.Assert(e0 != null || e1 != null);
			   e = new SeqSelectExpr(x, false, e, e0, e1);
			 } else if (multipleLengths != null) {
			   Expression prev = null;
			   List<Expression> seqs = new List<Expression>();
			    foreach (var len in multipleLengths) {
			      var end = prev == null ? len : new BinaryExpr(x, BinaryExpr.Opcode.Add, prev, len);
			      seqs.Add(new SeqSelectExpr(x, false, e, prev, end));
			      prev = end;
			    }
			   if (takeRest) {
			     seqs.Add(new SeqSelectExpr(x, false, e, prev, null));
			   }
			   e = new SeqDisplayExpr(x, seqs);
			 } else if (e1 == null) {
			   Contract.Assert(e0 != null);
			   e = new SeqSelectExpr(x, true, e, e0, null);
			 } else {
			   Contract.Assert(e0 != null);
			   e = new SeqUpdateExpr(x, e, e0, e1);
			 }
			}
			
			Expect(49);
		} else if (la.kind == 50) {
			Get();
			IToken openParen = t; var args = new List<Expression>(); 
			if (StartOf(9)) {
				Expressions(args);
			}
			Expect(51);
			e = new ApplySuffix(openParen, e, args); 
		} else SynErr(237);
	}

	void ISetDisplayExpr(IToken/*!*/ setToken, bool finite, out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		List<Expression> elements = new List<Expression/*!*/>();;
		e = dummyExpr;
		
		Expect(46);
		if (StartOf(9)) {
			Expressions(elements);
		}
		e = new SetDisplayExpr(setToken, finite, elements);
		Expect(47);
	}

	void LambdaExpression(out Expression e, bool allowSemi) {
		IToken x = Token.NoToken;
		IToken id;  BoundVar bv;
		var bvs = new List<BoundVar>();
		FrameExpression fe;  Expression ee;
		var reads = new List<FrameExpression>();
		Expression req = null;
		bool oneShot;
		Expression body = null;
		
		if (la.kind == 1) {
			WildIdent(out id, true);
			x = t; bvs.Add(new BoundVar(id, id.val, new InferredTypeProxy())); 
		} else if (la.kind == 50) {
			Get();
			x = t; 
			if (la.kind == 1) {
				IdentTypeOptional(out bv);
				bvs.Add(bv); 
				while (la.kind == 22) {
					Get();
					IdentTypeOptional(out bv);
					bvs.Add(bv); 
				}
			}
			Expect(51);
		} else SynErr(238);
		while (la.kind == 44 || la.kind == 45) {
			if (la.kind == 44) {
				Get();
				PossiblyWildFrameExpression(out fe, true);
				reads.Add(fe); 
			} else {
				Get();
				Expression(out ee, true, false);
				req = req == null ? ee : new BinaryExpr(req.tok, BinaryExpr.Opcode.And, req, ee); 
			}
		}
		LambdaArrow(out oneShot);
		Expression(out body, allowSemi, true);
		e = new LambdaExpr(x, oneShot, bvs, req, reads, body);
		theBuiltIns.CreateArrowTypeDecl(bvs.Count);
		
	}

	void EndlessExpression(out Expression e, bool allowSemi, bool allowLambda) {
		IToken/*!*/ x;
		Expression e0, e1;
		Statement s;
		bool isExistentialGuard = false;
		e = dummyExpr;
		
		switch (la.kind) {
		case 102: {
			Get();
			x = t; 
			if (IsExistentialGuard()) {
				ExistentialGuard(out e, true);
				isExistentialGuard = true; 
			} else if (StartOf(9)) {
				Expression(out e, true, true);
			} else SynErr(239);
			Expect(34);
			Expression(out e0, true, true);
			Expect(35);
			Expression(out e1, allowSemi, allowLambda);
			if (isExistentialGuard) {
			 var exists = (ExistsExpr) e;
			 List<CasePattern> LHSs = new List<CasePattern>();
			 foreach (var v in exists.BoundVars) {
			   LHSs.Add(new CasePattern(e.tok, v));
			 }
			 e0 = new LetExpr(e.tok, LHSs, new List<Expression>() { exists.Term }, e0, false);	                                                         
			}
			e = new ITEExpr(x, isExistentialGuard, e, e0, e1);
			
			break;
		}
		case 104: {
			MatchExpression(out e, allowSemi, allowLambda);
			break;
		}
		case 107: case 127: case 128: case 129: {
			QuantifierGuts(out e, allowSemi, allowLambda);
			break;
		}
		case 13: {
			Get();
			x = t; 
			SetComprehensionExpr(x, true, out e, allowSemi, allowLambda);
			break;
		}
		case 14: {
			Get();
			x = t; 
			SetComprehensionExpr(x, false, out e, allowSemi, allowLambda);
			break;
		}
		case 31: case 32: case 105: {
			StmtInExpr(out s);
			Expression(out e, allowSemi, allowLambda);
			e = new StmtExpr(s.Tok, s, e); 
			break;
		}
		case 62: case 82: {
			LetExpr(out e, allowSemi, allowLambda);
			break;
		}
		case 17: {
			Get();
			x = t; 
			MapComprehensionExpr(x, true, out e, allowSemi, allowLambda);
			break;
		}
		case 18: {
			Get();
			x = t; 
			MapComprehensionExpr(x, false, out e, allowSemi, allowLambda);
			break;
		}
		case 96: {
			NamedExpr(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(240); break;
		}
	}

	void NameSegment(out Expression e) {
		IToken id;
		IToken openParen = null;  List<Type> typeArgs = null;  List<Expression> args = null;
		
		Ident(out id);
		if (IsGenericInstantiation()) {
			typeArgs = new List<Type>(); 
			GenericInstantiation(typeArgs);
		} else if (la.kind == 110) {
			HashCall(id, out openParen, out typeArgs, out args);
		} else if (StartOf(33)) {
		} else SynErr(241);
		e = new NameSegment(id, id.val, typeArgs);
		if (openParen != null) {
		 e = new ApplySuffix(openParen, e, args);
		}
		
	}

	void DisplayExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken x;  List<Expression> elements;
		e = dummyExpr;
		
		if (la.kind == 46) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(9)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, true, elements);
			Expect(47);
		} else if (la.kind == 48) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(9)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(49);
		} else SynErr(242);
	}

	void MultiSetExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		Expect(15);
		x = t; 
		if (la.kind == 46) {
			Get();
			elements = new List<Expression/*!*/>(); 
			if (StartOf(9)) {
				Expressions(elements);
			}
			e = new MultiSetDisplayExpr(x, elements);
			Expect(47);
		} else if (la.kind == 50) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			Expression(out e, true, true);
			e = new MultiSetFormingExpr(x, e); 
			Expect(51);
		} else SynErr(243);
	}

	void ConstAtomExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;   Basetypes.BigDec d;
		e = dummyExpr;  Type toType = null;
		
		switch (la.kind) {
		case 135: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 136: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 137: {
			Get();
			e = new LiteralExpr(t); 
			break;
		}
		case 2: case 3: {
			Nat(out n);
			e = new LiteralExpr(t, n); 
			break;
		}
		case 4: {
			Dec(out d);
			e = new LiteralExpr(t, d); 
			break;
		}
		case 19: {
			Get();
			e = new CharLiteralExpr(t, t.val.Substring(1, t.val.Length - 2)); 
			break;
		}
		case 20: {
			Get();
			bool isVerbatimString;
			string s = Util.RemoveParsedStringQuotes(t.val, out isVerbatimString);
			e = new StringLiteralExpr(t, s, isVerbatimString);
			
			break;
		}
		case 138: {
			Get();
			e = new ThisExpr(t); 
			break;
		}
		case 139: {
			Get();
			x = t; 
			Expect(50);
			Expression(out e, true, true);
			Expect(51);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Fresh, e); 
			break;
		}
		case 140: {
			Get();
			x = t; 
			Expect(50);
			Expression(out e, true, true);
			Expect(51);
			e = new OldExpr(x, e); 
			break;
		}
		case 23: {
			Get();
			x = t; 
			Expression(out e, true, true);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Cardinality, e); 
			Expect(23);
			break;
		}
		case 8: case 10: {
			if (la.kind == 8) {
				Get();
				x = t; toType = new IntType(); 
			} else {
				Get();
				x = t; toType = new RealType(); 
			}
			Expect(50);
			Expression(out e, true, true);
			Expect(51);
			e = new ConversionExpr(x, e, toType); 
			break;
		}
		case 50: {
			ParensExpression(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(244); break;
		}
	}

	void Nat(out BigInteger n) {
		n = BigInteger.Zero;
		string S;
		
		if (la.kind == 2) {
			Get();
			S = Util.RemoveUnderscores(t.val);
			try {
			 n = BigIntegerParser.Parse(S);
			} catch (System.FormatException) {
			 SemErr("incorrectly formatted number");
			 n = BigInteger.Zero;
			}
			
		} else if (la.kind == 3) {
			Get();
			S = Util.RemoveUnderscores(t.val.Substring(2));
			try {
			 // note: leading 0 required when parsing positive hex numbers
			 n = BigIntegerParser.Parse("0" + S, System.Globalization.NumberStyles.HexNumber);
			} catch (System.FormatException) {
			 SemErr("incorrectly formatted number");
			 n = BigInteger.Zero;
			}
			
		} else SynErr(245);
	}

	void Dec(out Basetypes.BigDec d) {
		d = Basetypes.BigDec.ZERO; 
		Expect(4);
		var S = Util.RemoveUnderscores(t.val);
		try {
		 d = Basetypes.BigDec.FromString(S);
		} catch (System.FormatException) {
		 SemErr("incorrectly formatted number");
		 d = Basetypes.BigDec.ZERO;
		}
		
	}

	void ParensExpression(out Expression e, bool allowSemi, bool allowLambda) {
		IToken x;
		var args = new List<Expression>();
		
		Expect(50);
		x = t; 
		if (StartOf(9)) {
			Expressions(args);
		}
		Expect(51);
		if (args.Count == 1) {
		 e = new ParensExpression(x, args[0]);
		} else {
		 // make sure the corresponding tuple type exists
		 var tmp = theBuiltIns.TupleType(x, args.Count, true);
		 e = new DatatypeValue(x, BuiltIns.TupleTypeName(args.Count), BuiltIns.TupleTypeCtorName, args);
		}
		
	}

	void LambdaArrow(out bool oneShot) {
		oneShot = true; 
		if (la.kind == 29) {
			Get();
			oneShot = false; 
		} else if (la.kind == 30) {
			Get();
			oneShot = true; 
		} else SynErr(246);
	}

	void MapLiteralExpressions(out List<ExpressionPair> elements) {
		Expression/*!*/ d, r;
		elements = new List<ExpressionPair/*!*/>(); 
		Expression(out d, true, true);
		Expect(99);
		Expression(out r, true, true);
		elements.Add(new ExpressionPair(d,r)); 
		while (la.kind == 22) {
			Get();
			Expression(out d, true, true);
			Expect(99);
			Expression(out r, true, true);
			elements.Add(new ExpressionPair(d,r)); 
		}
	}

	void MapComprehensionExpr(IToken mapToken, bool finite, out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		BoundVar bv;
		List<BoundVar> bvars = new List<BoundVar>();
		Expression range = null;
		Expression body;
		Attributes attrs = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		if (la.kind == 23) {
			Get();
			Expression(out range, true, true);
		}
		QSep();
		Expression(out body, allowSemi, allowLambda);
		e = new MapComprehension(mapToken, finite, bvars, range ?? new LiteralExpr(mapToken, true), body, attrs);
		
	}

	void MatchExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  MatchCaseExpr/*!*/ c;
		List<MatchCaseExpr/*!*/> cases = new List<MatchCaseExpr/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(104);
		x = t; 
		Expression(out e, allowSemi, allowLambda);
		if (la.kind == _lbrace) {
			Expect(46);
			usesOptionalBrace = true; 
			while (la.kind == 33) {
				CaseExpression(out c, true, true);
				cases.Add(c); 
			}
			Expect(47);
		} else if (StartOf(34)) {
			while (la.kind == _case) {
				CaseExpression(out c, allowSemi, allowLambda);
				cases.Add(c); 
			}
		} else SynErr(247);
		e = new MatchExpr(x, e, cases, usesOptionalBrace); 
	}

	void QuantifierGuts(out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		List<BoundVar/*!*/> bvars;
		Attributes attrs;
		Expression range;
		Expression/*!*/ body;
		
		if (la.kind == 107 || la.kind == 127) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 128 || la.kind == 129) {
			Exists();
			x = t; 
		} else SynErr(248);
		QuantifierDomain(out bvars, out attrs, out range);
		QSep();
		Expression(out body, allowSemi, allowLambda);
		if (univ) {
		 q = new ForallExpr(x, bvars, range, body, attrs);
		} else {
		 q = new ExistsExpr(x, bvars, range, body, attrs);
		}
		
	}

	void SetComprehensionExpr(IToken setToken, bool finite, out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null);
		BoundVar bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar>();
		Expression range;
		Expression body = null;
		Attributes attrs = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 22) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (la.kind == 46) {
			Attribute(ref attrs);
		}
		Expect(23);
		Expression(out range, allowSemi, allowLambda);
		if (IsQSep()) {
			QSep();
			Expression(out body, allowSemi, allowLambda);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(setToken, finite, bvars, range, body, attrs);
		
	}

	void StmtInExpr(out Statement s) {
		s = dummyStmt; 
		if (la.kind == 105) {
			AssertStmt(out s);
		} else if (la.kind == 31) {
			AssumeStmt(out s);
		} else if (la.kind == 32) {
			CalcStmt(out s);
		} else SynErr(249);
	}

	void LetExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken x = null;
		bool isGhost = false;
		var letLHSs = new List<CasePattern>();
		var letRHSs = new List<Expression>();
		CasePattern pat;
		bool exact = true;
		Attributes attrs = null;
		e = dummyExpr;
		
		if (la.kind == 62) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(82);
		if (!isGhost) { x = t; } 
		CasePattern(out pat);
		if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
		letLHSs.Add(pat);
		
		while (la.kind == 22) {
			Get();
			CasePattern(out pat);
			if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
			letLHSs.Add(pat);
			
		}
		if (la.kind == 99) {
			Get();
		} else if (la.kind == 25 || la.kind == 46) {
			while (la.kind == 46) {
				Attribute(ref attrs);
			}
			Expect(25);
			exact = false;
			foreach (var lhs in letLHSs) {
			 if (lhs.Arguments != null) {
			   SemErr(lhs.tok, "LHS of let-such-that expression must be variables, not general patterns");
			 }
			}
			
		} else SynErr(250);
		Expression(out e, false, true);
		letRHSs.Add(e); 
		while (la.kind == 22) {
			Get();
			Expression(out e, false, true);
			letRHSs.Add(e); 
		}
		Expect(28);
		Expression(out e, allowSemi, allowLambda);
		e = new LetExpr(x, letLHSs, letRHSs, e, exact, attrs); 
	}

	void NamedExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken/*!*/ x, d;
		e = dummyExpr;
		Expression expr;
		
		Expect(96);
		x = t; 
		NoUSIdent(out d);
		Expect(21);
		Expression(out e, allowSemi, allowLambda);
		expr = e;
		e = new NamedExpr(x, d.val, expr); 
	}

	void CaseExpression(out MatchCaseExpr c, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id;
		List<CasePattern/*!*/> arguments = new List<CasePattern/*!*/>();
		CasePattern/*!*/ pat;
		Expression/*!*/ body;
		string/*!*/ name = "";
		
		Expect(33);
		x = t; 
		if (la.kind == 1) {
			Ident(out id);
			name = id.val; 
			if (la.kind == 50) {
				Get();
				if (la.kind == 1 || la.kind == 50) {
					CasePattern(out pat);
					arguments.Add(pat); 
					while (la.kind == 22) {
						Get();
						CasePattern(out pat);
						arguments.Add(pat); 
					}
				}
				Expect(51);
			}
		} else if (la.kind == 50) {
			Get();
			CasePattern(out pat);
			arguments.Add(pat); 
			while (la.kind == 22) {
				Get();
				CasePattern(out pat);
				arguments.Add(pat); 
			}
			Expect(51);
		} else SynErr(251);
		Expect(29);
		Expression(out body, allowSemi, allowLambda);
		c = new MatchCaseExpr(x, name, arguments, body); 
	}

	void HashCall(IToken id, out IToken openParen, out List<Type> typeArgs, out List<Expression> args) {
		Expression k; args = new List<Expression>(); typeArgs = null; 
		Expect(110);
		id.val = id.val + "#"; 
		if (la.kind == 52) {
			typeArgs = new List<Type>(); 
			GenericInstantiation(typeArgs);
		}
		Expect(48);
		Expression(out k, true, true);
		Expect(49);
		args.Add(k); 
		Expect(50);
		openParen = t; 
		if (StartOf(9)) {
			Expressions(args);
		}
		Expect(51);
	}

	void MemberBindingUpdate(out IToken id, out Expression e) {
		id = Token.NoToken; e = dummyExpr; 
		if (la.kind == 1) {
			Get();
			id = t; 
		} else if (la.kind == 2) {
			Get();
			id = t; 
		} else SynErr(252);
		Expect(99);
		Expression(out e, true, true);
	}

	void DotSuffix(out IToken x, out IToken y) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		x = Token.NoToken;
		y = null;
		
		if (la.kind == 1) {
			Get();
			x = t; 
		} else if (la.kind == 2) {
			Get();
			x = t; 
		} else if (la.kind == 4) {
			Get();
			x = t;
			int exponent = x.val.IndexOf('e');
			if (0 <= exponent) {
			 // this is not a legal field/destructor name
			 SemErr(x, "invalid DotSuffix");
			} else {
			 int dot = x.val.IndexOf('.');
			 if (0 <= dot) {
			   y = new Token();
			   y.pos = x.pos + dot + 1;
			   y.val = x.val.Substring(dot + 1);
			   x.val = x.val.Substring(0, dot);
			   y.col = x.col + dot + 1;
			   y.line = x.line;
			   y.filename = x.filename;
			   y.kind = x.kind;
			 }
			}
			
		} else if (la.kind == 45) {
			Get();
			x = t; 
		} else if (la.kind == 44) {
			Get();
			x = t; 
		} else SynErr(253);
	}



	public void Parse() {
		la = new Token();
		la.val = "";
		Get();
		Dafny();
		Expect(0);

	}

	static readonly bool[,] set = {
		{_T,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _T,_x,_x,_T, _T,_T,_x,_x, _T,_T,_x,_x, _T,_T,_x,_T, _T,_T,_T,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _T,_T,_T,_x, _x,_T,_x,_x, _T,_T,_T,_T, _T,_T,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_T,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _T,_T,_T,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _T,_T,_T,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_x,_x, _x,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _T,_T,_T,_x, _x,_x,_x,_T, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_T,_x, _x,_T,_x,_T, _x,_x,_T,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _T,_T,_T,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_T,_T,_T, _x,_T,_T,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _T,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_T,_T, _T,_T,_T,_x, _T,_T,_T,_T, _x,_x,_T,_x, _T,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_T,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _T,_T,_T,_T, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_T, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_x, _x,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_T, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_T,_T,_T, _x,_T,_T,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _T,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_T,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_T,_T,_T, _x,_T,_T,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_T,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _T,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_T,_T,_T, _x,_T,_T,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _T,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_T,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_T,_T,_T, _x,_T,_T,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_T,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_T, _T,_T,_x,_x, _T,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_x,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_T,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_T, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_x, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_x,_x},
		{_x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_T,_T,_x, _x,_T,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_x,_x,_x, _x,_x,_T,_x, _T,_T,_x,_T, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_x,_T,_T,_x, _T,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _T,_T,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x, _x,_x,_x,_x},
		{_T,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _x,_T,_T,_T, _T,_T,_T,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_T, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x},
		{_T,_T,_T,_T, _T,_x,_x,_x, _T,_x,_T,_x, _x,_x,_x,_x, _x,_x,_x,_T, _T,_T,_T,_T, _T,_x,_T,_x, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _x,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _x,_T,_T,_T, _T,_T,_T,_x, _x,_T,_x,_x, _x,_x,_T,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_T, _T,_x,_T,_T, _T,_T,_T,_T, _T,_T,_x,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x, _x,_x,_T,_T, _T,_T,_T,_T, _T,_T,_T,_T, _T,_T,_x,_x}

	};
} // end Parser


public class Errors {
	readonly ErrorReporter Reporting;
	public int ErrorCount;

	public Errors(ErrorReporter Reporting) {
		Contract.Requires(Reporting != null);
		this.Reporting = Reporting;
	}

	public void SynErr(string filename, int line, int col, int n) {
		SynErr(filename, line, col, GetSyntaxErrorString(n));
	}

	public void SynErr(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		ErrorCount++;
		Reporting.Error(MessageSource.Parser, filename, line, col, msg);
	}

	string GetSyntaxErrorString(int n) {
		string s;
		switch (n) {
			case 0: s = "EOF expected"; break;
			case 1: s = "ident expected"; break;
			case 2: s = "digits expected"; break;
			case 3: s = "hexdigits expected"; break;
			case 4: s = "decimaldigits expected"; break;
			case 5: s = "arrayToken expected"; break;
			case 6: s = "bool expected"; break;
			case 7: s = "char expected"; break;
			case 8: s = "int expected"; break;
			case 9: s = "nat expected"; break;
			case 10: s = "real expected"; break;
			case 11: s = "object expected"; break;
			case 12: s = "string expected"; break;
			case 13: s = "set expected"; break;
			case 14: s = "iset expected"; break;
			case 15: s = "multiset expected"; break;
			case 16: s = "seq expected"; break;
			case 17: s = "map expected"; break;
			case 18: s = "imap expected"; break;
			case 19: s = "charToken expected"; break;
			case 20: s = "stringToken expected"; break;
			case 21: s = "colon expected"; break;
			case 22: s = "comma expected"; break;
			case 23: s = "verticalbar expected"; break;
			case 24: s = "doublecolon expected"; break;
			case 25: s = "boredSmiley expected"; break;
			case 26: s = "bullet expected"; break;
			case 27: s = "dot expected"; break;
			case 28: s = "semi expected"; break;
			case 29: s = "darrow expected"; break;
			case 30: s = "arrow expected"; break;
			case 31: s = "assume expected"; break;
			case 32: s = "calc expected"; break;
			case 33: s = "case expected"; break;
			case 34: s = "then expected"; break;
			case 35: s = "else expected"; break;
			case 36: s = "decreases expected"; break;
			case 37: s = "invariant expected"; break;
			case 38: s = "function expected"; break;
			case 39: s = "predicate expected"; break;
			case 40: s = "inductive expected"; break;
			case 41: s = "lemma expected"; break;
			case 42: s = "copredicate expected"; break;
			case 43: s = "modifies expected"; break;
			case 44: s = "reads expected"; break;
			case 45: s = "requires expected"; break;
			case 46: s = "lbrace expected"; break;
			case 47: s = "rbrace expected"; break;
			case 48: s = "lbracket expected"; break;
			case 49: s = "rbracket expected"; break;
			case 50: s = "openparen expected"; break;
			case 51: s = "closeparen expected"; break;
			case 52: s = "openAngleBracket expected"; break;
			case 53: s = "closeAngleBracket expected"; break;
			case 54: s = "eq expected"; break;
			case 55: s = "neq expected"; break;
			case 56: s = "neqAlt expected"; break;
			case 57: s = "star expected"; break;
			case 58: s = "notIn expected"; break;
			case 59: s = "ellipsis expected"; break;
			case 60: s = "\"include\" expected"; break;
			case 61: s = "\"abstract\" expected"; break;
			case 62: s = "\"ghost\" expected"; break;
			case 63: s = "\"static\" expected"; break;
			case 64: s = "\"protected\" expected"; break;
			case 65: s = "\"extern\" expected"; break;
			case 66: s = "\"module\" expected"; break;
			case 67: s = "\"exclusively\" expected"; break;
			case 68: s = "\"refines\" expected"; break;
			case 69: s = "\"import\" expected"; break;
			case 70: s = "\"opened\" expected"; break;
			case 71: s = "\"=\" expected"; break;
			case 72: s = "\"as\" expected"; break;
			case 73: s = "\"default\" expected"; break;
			case 74: s = "\"export\" expected"; break;
			case 75: s = "\"opaque\" expected"; break;
			case 76: s = "\"reveal\" expected"; break;
			case 77: s = "\"extends\" expected"; break;
			case 78: s = "\"class\" expected"; break;
			case 79: s = "\"trait\" expected"; break;
			case 80: s = "\"datatype\" expected"; break;
			case 81: s = "\"codatatype\" expected"; break;
			case 82: s = "\"var\" expected"; break;
			case 83: s = "\"newtype\" expected"; break;
			case 84: s = "\"type\" expected"; break;
			case 85: s = "\"iterator\" expected"; break;
			case 86: s = "\"yields\" expected"; break;
			case 87: s = "\"returns\" expected"; break;
			case 88: s = "\"method\" expected"; break;
			case 89: s = "\"colemma\" expected"; break;
			case 90: s = "\"comethod\" expected"; break;
			case 91: s = "\"constructor\" expected"; break;
			case 92: s = "\"free\" expected"; break;
			case 93: s = "\"ensures\" expected"; break;
			case 94: s = "\"yield\" expected"; break;
			case 95: s = "\"`\" expected"; break;
			case 96: s = "\"label\" expected"; break;
			case 97: s = "\"break\" expected"; break;
			case 98: s = "\"where\" expected"; break;
			case 99: s = "\":=\" expected"; break;
			case 100: s = "\"return\" expected"; break;
			case 101: s = "\"new\" expected"; break;
			case 102: s = "\"if\" expected"; break;
			case 103: s = "\"while\" expected"; break;
			case 104: s = "\"match\" expected"; break;
			case 105: s = "\"assert\" expected"; break;
			case 106: s = "\"print\" expected"; break;
			case 107: s = "\"forall\" expected"; break;
			case 108: s = "\"parallel\" expected"; break;
			case 109: s = "\"modify\" expected"; break;
			case 110: s = "\"#\" expected"; break;
			case 111: s = "\"<=\" expected"; break;
			case 112: s = "\">=\" expected"; break;
			case 113: s = "\"\\u2264\" expected"; break;
			case 114: s = "\"\\u2265\" expected"; break;
			case 115: s = "\"<==>\" expected"; break;
			case 116: s = "\"\\u21d4\" expected"; break;
			case 117: s = "\"==>\" expected"; break;
			case 118: s = "\"\\u21d2\" expected"; break;
			case 119: s = "\"<==\" expected"; break;
			case 120: s = "\"\\u21d0\" expected"; break;
			case 121: s = "\"&&\" expected"; break;
			case 122: s = "\"\\u2227\" expected"; break;
			case 123: s = "\"||\" expected"; break;
			case 124: s = "\"\\u2228\" expected"; break;
			case 125: s = "\"!\" expected"; break;
			case 126: s = "\"\\u00ac\" expected"; break;
			case 127: s = "\"\\u2200\" expected"; break;
			case 128: s = "\"exists\" expected"; break;
			case 129: s = "\"\\u2203\" expected"; break;
			case 130: s = "\"in\" expected"; break;
			case 131: s = "\"+\" expected"; break;
			case 132: s = "\"-\" expected"; break;
			case 133: s = "\"/\" expected"; break;
			case 134: s = "\"%\" expected"; break;
			case 135: s = "\"false\" expected"; break;
			case 136: s = "\"true\" expected"; break;
			case 137: s = "\"null\" expected"; break;
			case 138: s = "\"this\" expected"; break;
			case 139: s = "\"fresh\" expected"; break;
			case 140: s = "\"old\" expected"; break;
			case 141: s = "\"..\" expected"; break;
			case 142: s = "??? expected"; break;
			case 143: s = "invalid TopDecl"; break;
			case 144: s = "invalid DeclModifier"; break;
			case 145: s = "this symbol not expected in SubModuleDecl"; break;
			case 146: s = "invalid SubModuleDecl"; break;
			case 147: s = "this symbol not expected in ClassDecl"; break;
			case 148: s = "this symbol not expected in DatatypeDecl"; break;
			case 149: s = "invalid DatatypeDecl"; break;
			case 150: s = "this symbol not expected in DatatypeDecl"; break;
			case 151: s = "invalid NewtypeDecl"; break;
			case 152: s = "invalid OtherTypeDecl"; break;
			case 153: s = "this symbol not expected in OtherTypeDecl"; break;
			case 154: s = "this symbol not expected in IteratorDecl"; break;
			case 155: s = "invalid IteratorDecl"; break;
			case 156: s = "this symbol not expected in TraitDecl"; break;
			case 157: s = "invalid ClassMemberDecl"; break;
			case 158: s = "this symbol not expected in FieldDecl"; break;
			case 159: s = "invalid FunctionDecl"; break;
			case 160: s = "invalid FunctionDecl"; break;
			case 161: s = "invalid FunctionDecl"; break;
			case 162: s = "invalid FunctionDecl"; break;
			case 163: s = "invalid FunctionDecl"; break;
			case 164: s = "this symbol not expected in MethodDecl"; break;
			case 165: s = "invalid MethodDecl"; break;
			case 166: s = "invalid MethodDecl"; break;
			case 167: s = "invalid FIdentType"; break;
			case 168: s = "this symbol not expected in OldSemi"; break;
			case 169: s = "invalid TypeIdentOptional"; break;
			case 170: s = "invalid TypeAndToken"; break;
			case 171: s = "this symbol not expected in IteratorSpec"; break;
			case 172: s = "invalid IteratorSpec"; break;
			case 173: s = "invalid IteratorSpec"; break;
			case 174: s = "this symbol not expected in MethodSpec"; break;
			case 175: s = "invalid MethodSpec"; break;
			case 176: s = "invalid MethodSpec"; break;
			case 177: s = "invalid FrameExpression"; break;
			case 178: s = "this symbol not expected in FunctionSpec"; break;
			case 179: s = "invalid FunctionSpec"; break;
			case 180: s = "invalid PossiblyWildFrameExpression"; break;
			case 181: s = "invalid PossiblyWildExpression"; break;
			case 182: s = "this symbol not expected in OneStmt"; break;
			case 183: s = "invalid OneStmt"; break;
			case 184: s = "this symbol not expected in OneStmt"; break;
			case 185: s = "invalid OneStmt"; break;
			case 186: s = "invalid AssertStmt"; break;
			case 187: s = "invalid AssumeStmt"; break;
			case 188: s = "invalid UpdateStmt"; break;
			case 189: s = "invalid UpdateStmt"; break;
			case 190: s = "this symbol not expected in VarDeclStatement"; break;
			case 191: s = "invalid VarDeclStatement"; break;
			case 192: s = "invalid VarDeclStatement"; break;
			case 193: s = "invalid IfStmt"; break;
			case 194: s = "invalid IfStmt"; break;
			case 195: s = "invalid WhileStmt"; break;
			case 196: s = "invalid WhileStmt"; break;
			case 197: s = "invalid MatchStmt"; break;
			case 198: s = "invalid ForallStmt"; break;
			case 199: s = "invalid ForallStmt"; break;
			case 200: s = "invalid CalcStmt"; break;
			case 201: s = "invalid ModifyStmt"; break;
			case 202: s = "this symbol not expected in ModifyStmt"; break;
			case 203: s = "invalid ModifyStmt"; break;
			case 204: s = "invalid ReturnStmt"; break;
			case 205: s = "invalid Rhs"; break;
			case 206: s = "invalid Lhs"; break;
			case 207: s = "invalid CasePattern"; break;
			case 208: s = "invalid AlternativeBlock"; break;
			case 209: s = "invalid Guard"; break;
			case 210: s = "this symbol not expected in LoopSpec"; break;
			case 211: s = "this symbol not expected in LoopSpec"; break;
			case 212: s = "this symbol not expected in LoopSpec"; break;
			case 213: s = "invalid LoopSpec"; break;
			case 214: s = "invalid CaseStatement"; break;
			case 215: s = "this symbol not expected in CaseStatement"; break;
			case 216: s = "this symbol not expected in CaseStatement"; break;
			case 217: s = "invalid CalcOp"; break;
			case 218: s = "invalid EquivOp"; break;
			case 219: s = "invalid ImpliesOp"; break;
			case 220: s = "invalid ExpliesOp"; break;
			case 221: s = "invalid AndOp"; break;
			case 222: s = "invalid OrOp"; break;
			case 223: s = "invalid NegOp"; break;
			case 224: s = "invalid Forall"; break;
			case 225: s = "invalid Exists"; break;
			case 226: s = "invalid QSep"; break;
			case 227: s = "invalid ImpliesExpliesExpression"; break;
			case 228: s = "invalid LogicalExpression"; break;
			case 229: s = "invalid RelOp"; break;
			case 230: s = "invalid AddOp"; break;
			case 231: s = "invalid UnaryExpression"; break;
			case 232: s = "invalid MulOp"; break;
			case 233: s = "invalid Suffix"; break;
			case 234: s = "invalid Suffix"; break;
			case 235: s = "invalid Suffix"; break;
			case 236: s = "invalid Suffix"; break;
			case 237: s = "invalid Suffix"; break;
			case 238: s = "invalid LambdaExpression"; break;
			case 239: s = "invalid EndlessExpression"; break;
			case 240: s = "invalid EndlessExpression"; break;
			case 241: s = "invalid NameSegment"; break;
			case 242: s = "invalid DisplayExpr"; break;
			case 243: s = "invalid MultiSetExpr"; break;
			case 244: s = "invalid ConstAtomExpression"; break;
			case 245: s = "invalid Nat"; break;
			case 246: s = "invalid LambdaArrow"; break;
			case 247: s = "invalid MatchExpression"; break;
			case 248: s = "invalid QuantifierGuts"; break;
			case 249: s = "invalid StmtInExpr"; break;
			case 250: s = "invalid LetExpr"; break;
			case 251: s = "invalid CaseExpression"; break;
			case 252: s = "invalid MemberBindingUpdate"; break;
			case 253: s = "invalid DotSuffix"; break;

			default: s = "error " + n; break;
		}
		return s;
	}

	public void SemErr(IToken tok, string msg) {  // semantic errors
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		ErrorCount++;
		Reporting.Error(MessageSource.Parser, tok, msg);
	}

	public void SemErr(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		ErrorCount++;
		Reporting.Error(MessageSource.Parser, filename, line, col, msg);
	}

	public void Warning(IToken tok, string msg) {
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		Reporting.Warning(MessageSource.Parser, tok, msg);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}
}