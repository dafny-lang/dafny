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
	public const int _multiset = 14;
	public const int _seq = 15;
	public const int _map = 16;
	public const int _charToken = 17;
	public const int _stringToken = 18;
	public const int _colon = 19;
	public const int _comma = 20;
	public const int _verticalbar = 21;
	public const int _doublecolon = 22;
	public const int _bullet = 23;
	public const int _dot = 24;
	public const int _semi = 25;
	public const int _darrow = 26;
	public const int _arrow = 27;
	public const int _assume = 28;
	public const int _calc = 29;
	public const int _case = 30;
	public const int _then = 31;
	public const int _else = 32;
	public const int _decreases = 33;
	public const int _invariant = 34;
	public const int _modifies = 35;
	public const int _reads = 36;
	public const int _requires = 37;
	public const int _lbrace = 38;
	public const int _rbrace = 39;
	public const int _lbracket = 40;
	public const int _rbracket = 41;
	public const int _openparen = 42;
	public const int _closeparen = 43;
	public const int _openAngleBracket = 44;
	public const int _closeAngleBracket = 45;
	public const int _eq = 46;
	public const int _neq = 47;
	public const int _neqAlt = 48;
	public const int _star = 49;
	public const int _notIn = 50;
	public const int _ellipsis = 51;
	public const int maxT = 133;

	const bool T = true;
	const bool x = false;
	const int minErrDist = 2;

	public Scanner/*!*/ scanner;
	public Errors/*!*/  errors;

	public Token/*!*/ t;    // last recognized token
	public Token/*!*/ la;   // lookahead token
	int errDist = minErrDist;

readonly Expression/*!*/ dummyExpr;
readonly AssignmentRhs/*!*/ dummyRhs;
readonly FrameExpression/*!*/ dummyFrameExpr;
readonly Statement/*!*/ dummyStmt;
readonly ModuleDecl theModule;
readonly BuiltIns theBuiltIns;
readonly bool theVerifyThisFile;
int anonymousIds = 0;

struct MemberModifiers {
  public bool IsGhost;
  public bool IsStatic;
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
    return Parse(s, filename, module, builtIns, errors, verifyThisFile);
  } else {
    using (System.IO.StreamReader reader = new System.IO.StreamReader(filename)) {
      s = Microsoft.Boogie.ParserHelper.Fill(reader, new List<string>());
      return Parse(s, DafnyOptions.Clo.UseBaseNameForFileName ? Path.GetFileName(filename) : filename, module, builtIns, errors, verifyThisFile);
    }
  }
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "module".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ filename, ModuleDecl module, BuiltIns builtIns, bool verifyThisFile=true) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(module != null);
  Errors errors = new Errors();
  return Parse(s, filename, module, builtIns, errors, verifyThisFile);
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "module".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner with the given Errors sink.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ filename, ModuleDecl module, BuiltIns builtIns,
                         Errors/*!*/ errors, bool verifyThisFile=true) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(module != null);
  Contract.Requires(errors != null);
  byte[]/*!*/ buffer = cce.NonNull( UTF8Encoding.Default.GetBytes(s));
  MemoryStream ms = new MemoryStream(buffer,false);
  Scanner scanner = new Scanner(ms, errors, filename);
  Parser parser = new Parser(scanner, errors, module, builtIns, verifyThisFile);
  parser.Parse();
  return parser.errors.count;
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

bool IsLoopSpec() {
  return la.kind == _invariant | la.kind == _decreases | la.kind == _modifies;
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
bool IsTypeList(ref IToken pt) {
  if (pt.kind != _openAngleBracket) {
    return false;
  }
  pt = scanner.Peek();
  return IsTypeSequence(ref pt, _closeAngleBracket);
}
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
    case _multiset:
    case _seq:
    case _map:
      pt = scanner.Peek();
      return IsTypeList(ref pt);
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
      return IsTypeSequence(ref pt, _closeparen);
    default:
      return false;
  }
}

/*--------------------------------------------------------------------------*/


	public Parser(Scanner/*!*/ scanner, Errors/*!*/ errors) {
		this.scanner = scanner;
		this.errors = errors;
		Token/*!*/ tok = new Token();
		tok.val = "";
		this.la = tok;
		this.t = new Token(); // just to satisfy its non-null constraint
	}

	void SynErr (int n) {
		if (errDist >= minErrDist) errors.SynErr(la.filename, la.line, la.col, n);
		errDist = 0;
	}

	public void SemErr (string/*!*/ msg) {
		Contract.Requires(msg != null);
		if (errDist >= minErrDist) errors.SemErr(t, msg);
		errDist = 0;
	}

	public void SemErr(IToken/*!*/ tok, string/*!*/ msg) {
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
		ClassDecl/*!*/ c; DatatypeDecl/*!*/ dt; TopLevelDecl td; IteratorDecl iter;
		List<MemberDecl/*!*/> membersDefaultClass = new List<MemberDecl/*!*/>();
		ModuleDecl submodule;
		// to support multiple files, create a default module only if theModule is null
		DefaultModuleDecl defaultModule = (DefaultModuleDecl)((LiteralModuleDecl)theModule).ModuleDef;
		// theModule should be a DefaultModuleDecl (actually, the singular DefaultModuleDecl)
		TraitDecl/*!*/ trait;
		Contract.Assert(defaultModule != null);
		
		while (la.kind == 52) {
			Get();
			Expect(18);
			{
			 string parsedFile = t.filename;
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
			switch (la.kind) {
			case 53: case 54: case 56: {
				SubModuleDecl(defaultModule, out submodule);
				defaultModule.TopLevelDecls.Add(submodule); 
				break;
			}
			case 61: {
				ClassDecl(defaultModule, out c);
				defaultModule.TopLevelDecls.Add(c); 
				break;
			}
			case 66: case 67: {
				DatatypeDecl(defaultModule, out dt);
				defaultModule.TopLevelDecls.Add(dt); 
				break;
			}
			case 69: {
				NewtypeDecl(defaultModule, out td);
				defaultModule.TopLevelDecls.Add(td); 
				break;
			}
			case 70: {
				OtherTypeDecl(defaultModule, out td);
				defaultModule.TopLevelDecls.Add(td); 
				break;
			}
			case 71: {
				IteratorDecl(defaultModule, out iter);
				defaultModule.TopLevelDecls.Add(iter); 
				break;
			}
			case 63: {
				TraitDecl(defaultModule, out trait);
				defaultModule.TopLevelDecls.Add(trait); 
				break;
			}
			case 64: case 65: case 68: case 74: case 75: case 76: case 77: case 78: case 82: case 83: case 84: {
				ClassMemberDecl(membersDefaultClass, false, true);
				break;
			}
			}
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

	void SubModuleDecl(ModuleDefinition parent, out ModuleDecl submodule) {
		ClassDecl/*!*/ c; DatatypeDecl/*!*/ dt; TopLevelDecl td; IteratorDecl iter;
		Attributes attrs = null;  IToken/*!*/ id;
		TraitDecl/*!*/ trait;
		List<MemberDecl/*!*/> namedModuleDefaultClassMembers = new List<MemberDecl>();;
		List<IToken> idRefined = null, idPath = null, idAssignment = null;
		ModuleDefinition module;
		ModuleDecl sm;
		submodule = null; // appease compiler
		bool isAbstract = false;
		bool opened = false;
		
		if (la.kind == 53 || la.kind == 54) {
			if (la.kind == 53) {
				Get();
				isAbstract = true; 
			}
			Expect(54);
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 55) {
				Get();
				QualifiedModuleName(out idRefined);
			}
			module = new ModuleDefinition(id, id.val, isAbstract, false, idRefined == null ? null : idRefined, parent, attrs, false); 
			Expect(38);
			module.BodyStartTok = t; 
			while (StartOf(1)) {
				switch (la.kind) {
				case 53: case 54: case 56: {
					SubModuleDecl(module, out sm);
					module.TopLevelDecls.Add(sm); 
					break;
				}
				case 61: {
					ClassDecl(module, out c);
					module.TopLevelDecls.Add(c); 
					break;
				}
				case 63: {
					TraitDecl(module, out trait);
					module.TopLevelDecls.Add(trait); 
					break;
				}
				case 66: case 67: {
					DatatypeDecl(module, out dt);
					module.TopLevelDecls.Add(dt); 
					break;
				}
				case 69: {
					NewtypeDecl(module, out td);
					module.TopLevelDecls.Add(td); 
					break;
				}
				case 70: {
					OtherTypeDecl(module, out td);
					module.TopLevelDecls.Add(td); 
					break;
				}
				case 71: {
					IteratorDecl(module, out iter);
					module.TopLevelDecls.Add(iter); 
					break;
				}
				case 64: case 65: case 68: case 74: case 75: case 76: case 77: case 78: case 82: case 83: case 84: {
					ClassMemberDecl(namedModuleDefaultClassMembers, false, true);
					break;
				}
				}
			}
			Expect(39);
			module.BodyEndTok = t;
			module.TopLevelDecls.Add(new DefaultClassDecl(module, namedModuleDefaultClassMembers));
			submodule = new LiteralModuleDecl(module, parent); 
		} else if (la.kind == 56) {
			Get();
			if (la.kind == 57) {
				Get();
				opened = true;
			}
			NoUSIdent(out id);
			if (la.kind == 58 || la.kind == 59) {
				if (la.kind == 58) {
					Get();
					QualifiedModuleName(out idPath);
					submodule = new AliasModuleDecl(idPath, id, parent, opened); 
				} else {
					Get();
					QualifiedModuleName(out idPath);
					if (la.kind == 60) {
						Get();
						QualifiedModuleName(out idAssignment);
					}
					submodule = new ModuleFacadeDecl(idPath, id, parent, idAssignment, opened); 
				}
			}
			if (la.kind == 25) {
				while (!(la.kind == 0 || la.kind == 25)) {SynErr(134); Get();}
				Get();
			}
			if (submodule == null) {
			 idPath = new List<IToken>();
			 idPath.Add(id);
			 submodule = new AliasModuleDecl(idPath, id, parent, opened);
			}
			
		} else SynErr(135);
	}

	void ClassDecl(ModuleDefinition/*!*/ module, out ClassDecl/*!*/ c) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ id;
		Type trait = null;
		List<Type>/*!*/ traits = new List<Type>();
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		
		while (!(la.kind == 0 || la.kind == 61)) {SynErr(136); Get();}
		Expect(61);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 44) {
			GenericParameters(typeArgs);
		}
		if (la.kind == 62) {
			Get();
			Type(out trait);
			traits.Add(trait); 
			while (la.kind == 20) {
				Get();
				Type(out trait);
				traits.Add(trait); 
			}
		}
		Expect(38);
		bodyStart = t;  
		while (StartOf(2)) {
			ClassMemberDecl(members, true, false);
		}
		Expect(39);
		c = new ClassDecl(id, id.val, module, typeArgs, members, attrs, traits);
		c.BodyStartTok = bodyStart;
		c.BodyEndTok = t;
		
	}

	void DatatypeDecl(ModuleDefinition/*!*/ module, out DatatypeDecl/*!*/ dt) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out dt)!=null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<DatatypeCtor/*!*/> ctors = new List<DatatypeCtor/*!*/>();
		IToken bodyStart = Token.NoToken;  // dummy assignment
		bool co = false;
		
		while (!(la.kind == 0 || la.kind == 66 || la.kind == 67)) {SynErr(137); Get();}
		if (la.kind == 66) {
			Get();
		} else if (la.kind == 67) {
			Get();
			co = true; 
		} else SynErr(138);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 44) {
			GenericParameters(typeArgs);
		}
		Expect(58);
		bodyStart = t; 
		DatatypeMemberDecl(ctors);
		while (la.kind == 21) {
			Get();
			DatatypeMemberDecl(ctors);
		}
		if (la.kind == 25) {
			while (!(la.kind == 0 || la.kind == 25)) {SynErr(139); Get();}
			Get();
		}
		if (co) {
		 dt = new CoDatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		} else {
		 dt = new IndDatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		}
		dt.BodyStartTok = bodyStart;
		dt.BodyEndTok = t;
		
	}

	void NewtypeDecl(ModuleDefinition module, out TopLevelDecl td) {
		IToken id, bvId;
		Attributes attrs = null;
		td = null;
		Type baseType = null;
		Expression wh;
		
		Expect(69);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		Expect(58);
		if (IsIdentColonOrBar()) {
			NoUSIdent(out bvId);
			if (la.kind == 19) {
				Get();
				Type(out baseType);
			}
			if (baseType == null) { baseType = new OperationTypeProxy(true, true, false, false, false); } 
			Expect(21);
			Expression(out wh, false, true);
			td = new NewtypeDecl(id, id.val, module, new BoundVar(bvId, bvId.val, baseType), wh, attrs); 
		} else if (StartOf(3)) {
			Type(out baseType);
			td = new NewtypeDecl(id, id.val, module, baseType, attrs); 
		} else SynErr(140);
	}

	void OtherTypeDecl(ModuleDefinition module, out TopLevelDecl td) {
		IToken id;
		Attributes attrs = null;
		var eqSupport = TypeParameter.EqualitySupportValue.Unspecified;
		var typeArgs = new List<TypeParameter>();
		td = null;
		Type ty;
		
		Expect(70);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 42) {
			Get();
			Expect(46);
			Expect(43);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
			if (la.kind == 44) {
				GenericParameters(typeArgs);
			}
		} else if (StartOf(4)) {
			if (la.kind == 44) {
				GenericParameters(typeArgs);
			}
			if (la.kind == 58) {
				Get();
				Type(out ty);
				td = new TypeSynonymDecl(id, id.val, typeArgs, module, ty, attrs); 
			}
		} else SynErr(141);
		if (td == null) {
		 td = new OpaqueTypeDecl(id, id.val, module, eqSupport, typeArgs, attrs);
		}
		
		if (la.kind == 25) {
			while (!(la.kind == 0 || la.kind == 25)) {SynErr(142); Get();}
			Get();
		}
	}

	void IteratorDecl(ModuleDefinition module, out IteratorDecl/*!*/ iter) {
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
		
		while (!(la.kind == 0 || la.kind == 71)) {SynErr(143); Get();}
		Expect(71);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 42 || la.kind == 44) {
			if (la.kind == 44) {
				GenericParameters(typeArgs);
			}
			Formals(true, true, ins);
			if (la.kind == 72 || la.kind == 73) {
				if (la.kind == 72) {
					Get();
				} else {
					Get();
					SemErr(t, "iterators don't have a 'returns' clause; did you mean 'yields'?"); 
				}
				Formals(false, true, outs);
			}
		} else if (la.kind == 51) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(144);
		while (StartOf(5)) {
			IteratorSpec(reads, mod, decreases, req, ens, yieldReq, yieldEns, ref readsAttrs, ref modAttrs, ref decrAttrs);
		}
		if (la.kind == 38) {
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

	void TraitDecl(ModuleDefinition/*!*/ module, out TraitDecl/*!*/ trait) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out trait) != null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>(); //traits should not support type parameters at the moment
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		
		while (!(la.kind == 0 || la.kind == 63)) {SynErr(145); Get();}
		Expect(63);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 44) {
			GenericParameters(typeArgs);
		}
		Expect(38);
		bodyStart = t; 
		while (StartOf(2)) {
			ClassMemberDecl(members, true, false);
		}
		Expect(39);
		trait = new TraitDecl(id, id.val, module, typeArgs, members, attrs);
		trait.BodyStartTok = bodyStart;
		trait.BodyEndTok = t;
		
	}

	void ClassMemberDecl(List<MemberDecl> mm, bool allowConstructors, bool moduleLevelDecl) {
		Contract.Requires(cce.NonNullElements(mm));
		Method/*!*/ m;
		Function/*!*/ f;
		MemberModifiers mmod = new MemberModifiers();
		IToken staticToken = null;
		
		while (la.kind == 64 || la.kind == 65) {
			if (la.kind == 64) {
				Get();
				mmod.IsGhost = true; 
			} else {
				Get();
				mmod.IsStatic = true; staticToken = t; 
			}
		}
		if (la.kind == 68) {
			if (moduleLevelDecl) {
			 SemErr(la, "fields are not allowed to be declared at the module level; instead, wrap the field in a 'class' declaration");
			 mmod.IsStatic = false;
			}
			
			FieldDecl(mmod, mm);
		} else if (la.kind == 82 || la.kind == 83 || la.kind == 84) {
			if (moduleLevelDecl && staticToken != null) {
			 errors.Warning(staticToken, "module-level functions are always non-instance, so the 'static' keyword is not allowed here");
			 mmod.IsStatic = false;
			}
			
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (StartOf(6)) {
			if (moduleLevelDecl && staticToken != null) {
			 errors.Warning(staticToken, "module-level methods are always non-instance, so the 'static' keyword is not allowed here");
			 mmod.IsStatic = false;
			}
			
			MethodDecl(mmod, allowConstructors, out m);
			mm.Add(m); 
		} else SynErr(146);
	}

	void Attribute(ref Attributes attrs) {
		string name;
		var args = new List<Expression>();
		
		Expect(38);
		Expect(19);
		Expect(1);
		name = t.val; 
		if (StartOf(7)) {
			Expressions(args);
		}
		Expect(39);
		attrs = new Attributes(name, args, attrs); 
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
		while (la.kind == 24) {
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
		
		Expect(44);
		NoUSIdent(out id);
		eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
		if (la.kind == 42) {
			Get();
			Expect(46);
			Expect(43);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
		}
		typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		while (la.kind == 20) {
			Get();
			NoUSIdent(out id);
			eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
			if (la.kind == 42) {
				Get();
				Expect(46);
				Expect(43);
				eqSupport = TypeParameter.EqualitySupportValue.Required; 
			}
			typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		}
		Expect(45);
	}

	void Type(out Type ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; 
		TypeAndToken(out tok, out ty);
	}

	void FieldDecl(MemberModifiers mmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		IToken/*!*/ id;  Type/*!*/ ty;
		
		while (!(la.kind == 0 || la.kind == 68)) {SynErr(147); Get();}
		Expect(68);
		if (mmod.IsStatic) { SemErr(t, "fields cannot be declared 'static'"); }
		
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		FIdentType(out id, out ty);
		mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		while (la.kind == 20) {
			Get();
			FIdentType(out id, out ty);
			mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		}
		OldSemi();
	}

	void FunctionDecl(MemberModifiers mmod, out Function/*!*/ f) {
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
		bool isPredicate = false;  bool isCoPredicate = false;
		bool isFunctionMethod = false;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		IToken signatureEllipsis = null;
		bool missingOpenParen;
		
		if (la.kind == 82) {
			Get();
			if (la.kind == 74) {
				Get();
				isFunctionMethod = true; 
			}
			if (mmod.IsGhost) { SemErr(t, "functions cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 42 || la.kind == 44) {
				if (la.kind == 44) {
					GenericParameters(typeArgs);
				}
				Formals(true, isFunctionMethod, formals);
				Expect(19);
				Type(out returnType);
			} else if (la.kind == 51) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(148);
		} else if (la.kind == 83) {
			Get();
			isPredicate = true; 
			if (la.kind == 74) {
				Get();
				isFunctionMethod = true; 
			}
			if (mmod.IsGhost) { SemErr(t, "predicates cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (StartOf(8)) {
				if (la.kind == 44) {
					GenericParameters(typeArgs);
				}
				missingOpenParen = true; 
				if (la.kind == 42) {
					Formals(true, isFunctionMethod, formals);
					missingOpenParen = false; 
				}
				if (missingOpenParen) { errors.Warning(t, "with the new support of higher-order functions in Dafny, parentheses-less predicates are no longer supported; in the new syntax, parentheses are required for the declaration and uses of predicates, even if the predicate takes no additional arguments"); } 
				if (la.kind == 19) {
					Get();
					SemErr(t, "predicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 51) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(149);
		} else if (la.kind == 84) {
			Get();
			isCoPredicate = true; 
			if (mmod.IsGhost) { SemErr(t, "copredicates cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (StartOf(8)) {
				if (la.kind == 44) {
					GenericParameters(typeArgs);
				}
				missingOpenParen = true; 
				if (la.kind == 42) {
					Formals(true, isFunctionMethod, formals);
					missingOpenParen = false; 
				}
				if (missingOpenParen) { errors.Warning(t, "with the new support of higher-order functions in Dafny, parentheses-less co-predicates are no longer supported; in the new syntax, parentheses are required for the declaration and uses of predicates, even if the co-predicate takes no additional arguments"); } 
				if (la.kind == 19) {
					Get();
					SemErr(t, "copredicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 51) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(150);
		} else SynErr(151);
		decreases = isCoPredicate ? null : new List<Expression/*!*/>(); 
		while (StartOf(9)) {
			FunctionSpec(reqs, reads, ens, decreases);
		}
		if (la.kind == 38) {
			FunctionBody(out body, out bodyStart, out bodyEnd);
		}
		if (DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 && !Attributes.Contains(attrs, "axiom") && !Attributes.Contains(attrs, "imported")) {
		  SemErr(t, "a function with an ensures clause must have a body, unless given the :axiom attribute");
		}
		
		IToken tok = theVerifyThisFile ? id : new IncludeToken(id);
		if (isPredicate) {
		  f = new Predicate(tok, id.val, mmod.IsStatic, !isFunctionMethod, typeArgs, formals,
		                    reqs, reads, ens, new Specification<Expression>(decreases, null), body, Predicate.BodyOriginKind.OriginalOrInherited, attrs, signatureEllipsis);
		} else if (isCoPredicate) {
		  f = new CoPredicate(tok, id.val, mmod.IsStatic, typeArgs, formals,
		                    reqs, reads, ens, body, attrs, signatureEllipsis);
		} else {
		  f = new Function(tok, id.val, mmod.IsStatic, !isFunctionMethod, typeArgs, formals, returnType,
		                   reqs, reads, ens, new Specification<Expression>(decreases, null), body, attrs, signatureEllipsis);
		}
		f.BodyStartTok = bodyStart;
		f.BodyEndTok = bodyEnd;
		theBuiltIns.CreateArrowTypeDecl(formals.Count);
		if (isCoPredicate) {
		 // also create an arrow type for the corresponding prefix predicate
		 theBuiltIns.CreateArrowTypeDecl(formals.Count + 1);
		}
		
	}

	void MethodDecl(MemberModifiers mmod, bool allowConstructor, out Method/*!*/ m) {
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
		bool isCoLemma = false;
		IToken signatureEllipsis = null;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		
		while (!(StartOf(10))) {SynErr(152); Get();}
		if (la.kind == 74) {
			Get();
		} else if (la.kind == 75) {
			Get();
			isLemma = true; 
		} else if (la.kind == 76) {
			Get();
			isCoLemma = true; 
		} else if (la.kind == 77) {
			Get();
			isCoLemma = true;
			errors.Warning(t, "the 'comethod' keyword has been deprecated; it has been renamed to 'colemma'");
			
		} else if (la.kind == 78) {
			Get();
			if (allowConstructor) {
			 isConstructor = true;
			} else {
			 SemErr(t, "constructors are allowed only in classes");
			}
			
		} else SynErr(153);
		keywordToken = t; 
		if (isLemma) {
		 if (mmod.IsGhost) {
		   SemErr(t, "lemmas cannot be declared 'ghost' (they are automatically 'ghost')");
		 }
		} else if (isConstructor) {
		 if (mmod.IsGhost) {
		   SemErr(t, "constructors cannot be declared 'ghost'");
		 }
		 if (mmod.IsStatic) {
		   SemErr(t, "constructors cannot be declared 'static'");
		 }
		} else if (isCoLemma) {
		 if (mmod.IsGhost) {
		   SemErr(t, "colemmas cannot be declared 'ghost' (they are automatically 'ghost')");
		 }
		}
		
		while (la.kind == 38) {
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
		
		if (la.kind == 42 || la.kind == 44) {
			if (la.kind == 44) {
				GenericParameters(typeArgs);
			}
			Formals(true, !mmod.IsGhost, ins);
			if (la.kind == 73) {
				Get();
				if (isConstructor) { SemErr(t, "constructors cannot have out-parameters"); } 
				Formals(false, !mmod.IsGhost, outs);
			}
		} else if (la.kind == 51) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(154);
		while (StartOf(11)) {
			MethodSpec(req, mod, ens, dec, ref decAttrs, ref modAttrs);
		}
		if (la.kind == 38) {
			BlockStmt(out body, out bodyStart, out bodyEnd);
		}
		if (DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 && !Attributes.Contains(attrs, "axiom") && !Attributes.Contains(attrs, "imported") && !Attributes.Contains(attrs, "decl") && theVerifyThisFile) {
		  SemErr(t, "a method with an ensures clause must have a body, unless given the :axiom attribute");
		}
		
		IToken tok = theVerifyThisFile ? id : new IncludeToken(id);
		if (isConstructor) {
		 m = new Constructor(tok, hasName ? id.val : "_ctor", typeArgs, ins,
		                     req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else if (isCoLemma) {
		 m = new CoLemma(tok, id.val, mmod.IsStatic, typeArgs, ins, outs,
		                 req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else if (isLemma) {
		 m = new Lemma(tok, id.val, mmod.IsStatic, typeArgs, ins, outs,
		               req, new Specification<FrameExpression>(mod, modAttrs), ens, new Specification<Expression>(dec, decAttrs), body, attrs, signatureEllipsis);
		} else {
		 m = new Method(tok, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs,
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
		
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 42) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(42);
		if (StartOf(12)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 20) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(43);
	}

	void FIdentType(out IToken/*!*/ id, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		id = Token.NoToken;
		
		if (la.kind == 1) {
			WildIdent(out id, false);
		} else if (la.kind == 2) {
			Get();
			id = t; 
		} else SynErr(155);
		Expect(19);
		Type(out ty);
	}

	void OldSemi() {
		if (la.kind == 25) {
			while (!(la.kind == 0 || la.kind == 25)) {SynErr(156); Get();}
			Get();
		}
	}

	void Expression(out Expression e, bool allowSemi, bool allowLambda) {
		Expression e0; IToken endTok; 
		EquivExpression(out e, allowSemi, allowLambda);
		if (SemiFollowsCall(allowSemi, e)) {
			Expect(25);
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
		if (la.kind == 64) {
			Get();
			if (allowGhostKeyword) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
		}
		IdentType(out id, out ty, true);
	}

	void IdentType(out IToken/*!*/ id, out Type/*!*/ ty, bool allowWildcardId) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		WildIdent(out id, allowWildcardId);
		Expect(19);
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
		if (la.kind == 19) {
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
		if (la.kind == 19) {
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
		if (la.kind == 64) {
			Get();
			isGhost = true; 
		}
		if (StartOf(3)) {
			TypeAndToken(out id, out ty);
			if (la.kind == 19) {
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
			Expect(19);
			Type(out ty);
		} else SynErr(157);
		if (name != null) {
		 identName = name;
		} else {
		 identName = "#" + anonymousIds++;
		}
		
	}

	void TypeAndToken(out IToken tok, out Type ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok)!=null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type> gt = null;
		
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
		case 13: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 44) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("set type expects only one type argument");
			}
			ty = new SetType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 14: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 44) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("multiset type expects only one type argument");
			}
			ty = new MultiSetType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 15: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 44) {
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
			tok = t;  ty = new UserDefinedType(tok, tok.val, new List<Type>(), new List<IToken>()); 
			break;
		}
		case 16: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 44) {
				GenericInstantiation(gt);
			}
			if (gt.Count == 0) {
			 ty = new MapType(null, null);
			} else if (gt.Count != 2) {
			 SemErr("map type expects two type arguments");
			 ty = new MapType(gt[0], gt.Count == 1 ? new InferredTypeProxy() : gt[1]);
			} else {
			 ty = new MapType(gt[0], gt[1]);
			}
			
			break;
		}
		case 42: {
			Get();
			tok = t; gt = new List<Type>(); 
			if (StartOf(3)) {
				Type(out ty);
				gt.Add(ty); 
				while (la.kind == 20) {
					Get();
					Type(out ty);
					gt.Add(ty); 
				}
			}
			Expect(43);
			if (gt.Count == 1) {
			 // just return the type 'ty'
			} else {
			 // make sure the nullary tuple type exists
			 var dims = gt.Count;
			 var tmp = theBuiltIns.TupleType(tok, dims, true);
			 ty = new UserDefinedType(tok, BuiltIns.TupleTypeName(dims), gt, new List<IToken>());
			}
			
			break;
		}
		case 1: case 5: case 11: {
			ReferenceType(out tok, out ty);
			break;
		}
		default: SynErr(158); break;
		}
		if (la.kind == 27) {
			Type t2; 
			Get();
			tok = t; 
			Type(out t2);
			if (gt == null) {
			 gt = new List<Type>{ ty };
			}
			ty = new ArrowType(tok, gt, t2);
			theBuiltIns.CreateArrowTypeDecl(gt.Count);
			
		}
	}

	void Formals(bool incoming, bool allowGhostKeyword, List<Formal> formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken id;  Type ty;  bool isGhost; 
		Expect(42);
		if (la.kind == 1 || la.kind == 64) {
			GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 20) {
				Get();
				GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(43);
	}

	void IteratorSpec(List<FrameExpression/*!*/>/*!*/ reads, List<FrameExpression/*!*/>/*!*/ mod, List<Expression/*!*/> decreases,
List<MaybeFreeExpression/*!*/>/*!*/ req, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<MaybeFreeExpression/*!*/>/*!*/ yieldReq, List<MaybeFreeExpression/*!*/>/*!*/ yieldEns,
ref Attributes readsAttrs, ref Attributes modAttrs, ref Attributes decrAttrs) {
		Expression/*!*/ e; FrameExpression/*!*/ fe; bool isFree = false; bool isYield = false; Attributes ensAttrs = null;
		
		while (!(StartOf(13))) {SynErr(159); Get();}
		if (la.kind == 36) {
			Get();
			while (IsAttribute()) {
				Attribute(ref readsAttrs);
			}
			FrameExpression(out fe, false, false);
			reads.Add(fe); 
			while (la.kind == 20) {
				Get();
				FrameExpression(out fe, false, false);
				reads.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 35) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, false);
			mod.Add(fe); 
			while (la.kind == 20) {
				Get();
				FrameExpression(out fe, false, false);
				mod.Add(fe); 
			}
			OldSemi();
		} else if (StartOf(14)) {
			if (la.kind == 79) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			if (la.kind == 81) {
				Get();
				isYield = true; 
			}
			if (la.kind == 37) {
				Get();
				Expression(out e, false, false);
				OldSemi();
				if (isYield) {
				 yieldReq.Add(new MaybeFreeExpression(e, isFree));
				} else {
				 req.Add(new MaybeFreeExpression(e, isFree));
				}
				
			} else if (la.kind == 80) {
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
				
			} else SynErr(160);
		} else if (la.kind == 33) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decrAttrs);
			}
			DecreasesList(decreases, false, false);
			OldSemi();
		} else SynErr(161);
	}

	void BlockStmt(out BlockStmt/*!*/ block, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out block) != null);
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(38);
		bodyStart = t; 
		while (StartOf(15)) {
			Stmt(body);
		}
		Expect(39);
		bodyEnd = t;
		block = new BlockStmt(bodyStart, bodyEnd, body); 
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases, ref Attributes decAttrs, ref Attributes modAttrs) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false; Attributes ensAttrs = null;
		
		while (!(StartOf(16))) {SynErr(162); Get();}
		if (la.kind == 35) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, false);
			mod.Add(fe); 
			while (la.kind == 20) {
				Get();
				FrameExpression(out fe, false, false);
				mod.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 37 || la.kind == 79 || la.kind == 80) {
			if (la.kind == 79) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			if (la.kind == 37) {
				Get();
				Expression(out e, false, false);
				OldSemi();
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 80) {
				Get();
				while (IsAttribute()) {
					Attribute(ref ensAttrs);
				}
				Expression(out e, false, false);
				OldSemi();
				ens.Add(new MaybeFreeExpression(e, isFree, ensAttrs)); 
			} else SynErr(163);
		} else if (la.kind == 33) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decAttrs);
			}
			DecreasesList(decreases, true, false);
			OldSemi();
		} else SynErr(164);
	}

	void FrameExpression(out FrameExpression fe, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null);
		Expression/*!*/ e;
		IToken/*!*/ id;
		string fieldName = null;  IToken feTok = null;
		fe = null;
		
		if (StartOf(7)) {
			Expression(out e, allowSemi, allowLambda);
			feTok = e.tok; 
			if (la.kind == 85) {
				Get();
				Ident(out id);
				fieldName = id.val;  feTok = id; 
			}
			fe = new FrameExpression(feTok, e, fieldName); 
		} else if (la.kind == 85) {
			Get();
			Ident(out id);
			fieldName = id.val; 
			fe = new FrameExpression(id, new ImplicitThisExpr(id), fieldName); 
		} else SynErr(165);
	}

	void DecreasesList(List<Expression> decreases, bool allowWildcard, bool allowLambda) {
		Expression e; 
		PossiblyWildExpression(out e, allowLambda);
		if (!allowWildcard && e is WildcardExpr) {
		 SemErr(e.tok, "'decreases *' is allowed only on loops and tail-recursive methods");
		} else {
		 decreases.Add(e);
		}
		
		while (la.kind == 20) {
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
		Expect(44);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 20) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(45);
	}

	void ReferenceType(out IToken/*!*/ tok, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type> gt;
		List<IToken> path;
		
		if (la.kind == 11) {
			Get();
			tok = t;  ty = new ObjectType(); 
		} else if (la.kind == 5) {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 44) {
				GenericInstantiation(gt);
			}
			int dims = tok.val.Length == 5 ? 1 : int.Parse(tok.val.Substring(5));
			ty = theBuiltIns.ArrayType(tok, dims, gt, true);
			
		} else if (la.kind == 1) {
			Ident(out tok);
			gt = new List<Type>();
			path = new List<IToken>(); 
			while (la.kind == _dot) {
				path.Add(tok); 
				Expect(24);
				Ident(out tok);
			}
			if (la.kind == 44) {
				GenericInstantiation(gt);
			}
			ty = new UserDefinedType(tok, tok.val, gt, path); 
		} else SynErr(166);
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/> decreases) {
		Contract.Requires(cce.NonNullElements(reqs));
		Contract.Requires(cce.NonNullElements(reads));
		Contract.Requires(decreases == null || cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		while (!(StartOf(17))) {SynErr(167); Get();}
		if (la.kind == 37) {
			Get();
			Expression(out e, false, false);
			OldSemi();
			reqs.Add(e); 
		} else if (la.kind == 36) {
			Get();
			PossiblyWildFrameExpression(out fe, false);
			reads.Add(fe); 
			while (la.kind == 20) {
				Get();
				PossiblyWildFrameExpression(out fe, false);
				reads.Add(fe); 
			}
			OldSemi();
		} else if (la.kind == 80) {
			Get();
			Expression(out e, false, false);
			OldSemi();
			ens.Add(e); 
		} else if (la.kind == 33) {
			Get();
			if (decreases == null) {
			 SemErr(t, "'decreases' clauses are meaningless for copredicates, so they are not allowed");
			 decreases = new List<Expression/*!*/>();
			}
			
			DecreasesList(decreases, false, false);
			OldSemi();
		} else SynErr(168);
	}

	void FunctionBody(out Expression/*!*/ e, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); e = dummyExpr; 
		Expect(38);
		bodyStart = t; 
		Expression(out e, true, true);
		Expect(39);
		bodyEnd = t; 
	}

	void PossiblyWildFrameExpression(out FrameExpression fe, bool allowSemi) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); fe = dummyFrameExpr; 
		if (la.kind == 49) {
			Get();
			fe = new FrameExpression(t, new WildcardExpr(t), null); 
		} else if (StartOf(18)) {
			FrameExpression(out fe, allowSemi, false);
		} else SynErr(169);
	}

	void PossiblyWildExpression(out Expression e, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 49) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(7)) {
			Expression(out e, false, allowLambda);
		} else SynErr(170);
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
		
		while (!(StartOf(19))) {SynErr(171); Get();}
		switch (la.kind) {
		case 38: {
			BlockStmt(out bs, out bodyStart, out bodyEnd);
			s = bs; 
			break;
		}
		case 96: {
			AssertStmt(out s);
			break;
		}
		case 28: {
			AssumeStmt(out s);
			break;
		}
		case 97: {
			PrintStmt(out s);
			break;
		}
		case 1: case 2: case 3: case 4: case 8: case 10: case 17: case 18: case 21: case 42: case 126: case 127: case 128: case 129: case 130: case 131: {
			UpdateStmt(out s);
			break;
		}
		case 64: case 68: {
			VarDeclStatement(out s);
			break;
		}
		case 93: {
			IfStmt(out s);
			break;
		}
		case 94: {
			WhileStmt(out s);
			break;
		}
		case 95: {
			MatchStmt(out s);
			break;
		}
		case 98: case 99: {
			ForallStmt(out s);
			break;
		}
		case 29: {
			CalcStmt(out s);
			break;
		}
		case 100: {
			ModifyStmt(out s);
			break;
		}
		case 86: {
			Get();
			x = t; 
			NoUSIdent(out id);
			Expect(19);
			OneStmt(out s);
			s.Labels = new LList<Label>(new Label(x, id.val), s.Labels); 
			break;
		}
		case 87: {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				NoUSIdent(out id);
				label = id.val; 
			} else if (la.kind == 25 || la.kind == 87) {
				while (la.kind == 87) {
					Get();
					breakCount++; 
				}
			} else SynErr(172);
			while (!(la.kind == 0 || la.kind == 25)) {SynErr(173); Get();}
			Expect(25);
			s = label != null ? new BreakStmt(x, t, label) : new BreakStmt(x, t, breakCount); 
			break;
		}
		case 81: case 90: {
			ReturnStmt(out s);
			break;
		}
		case 51: {
			SkeletonStmt(out s);
			break;
		}
		default: SynErr(174); break;
		}
	}

	void AssertStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;
		Expression e = dummyExpr; Attributes attrs = null;
		IToken dotdotdot = null;
		
		Expect(96);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(7)) {
			Expression(out e, false, true);
		} else if (la.kind == 51) {
			Get();
			dotdotdot = t; 
		} else SynErr(175);
		Expect(25);
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
		
		Expect(28);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(7)) {
			Expression(out e, false, true);
		} else if (la.kind == 51) {
			Get();
			dotdotdot = t; 
		} else SynErr(176);
		Expect(25);
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
		
		Expect(97);
		x = t; 
		Expression(out e, false, true);
		args.Add(e); 
		while (la.kind == 20) {
			Get();
			Expression(out e, false, true);
			args.Add(e); 
		}
		Expect(25);
		s = new PrintStmt(x, t, args); 
	}

	void UpdateStmt(out Statement/*!*/ s) {
		List<Expression> lhss = new List<Expression>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		Expression e;  AssignmentRhs r;
		Expression lhs0;
		IToken x, endTok = Token.NoToken;
		Attributes attrs = null;
		IToken suchThatAssume = null;
		Expression suchThat = null;
		
		Lhs(out e);
		x = e.tok; 
		if (la.kind == 25 || la.kind == 38) {
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			Expect(25);
			endTok = t; rhss.Add(new ExprRhs(e, attrs)); 
		} else if (la.kind == 20 || la.kind == 89 || la.kind == 91) {
			lhss.Add(e);  lhs0 = e; 
			while (la.kind == 20) {
				Get();
				Lhs(out e);
				lhss.Add(e); 
			}
			if (la.kind == 89) {
				Get();
				x = t; 
				Rhs(out r, lhs0);
				rhss.Add(r); 
				while (la.kind == 20) {
					Get();
					Rhs(out r, lhs0);
					rhss.Add(r); 
				}
			} else if (la.kind == 91) {
				Get();
				x = t; 
				if (la.kind == _assume) {
					Expect(28);
					suchThatAssume = t; 
				}
				Expression(out suchThat, false, true);
			} else SynErr(177);
			Expect(25);
			endTok = t; 
		} else if (la.kind == 19) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(178);
		if (suchThat != null) {
		 s = new AssignSuchThatStmt(x, endTok, lhss, suchThat, suchThatAssume);
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
		AssignmentRhs r;  IdentifierExpr lhs0;
		List<LocalVariable> lhss = new List<LocalVariable>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		IToken suchThatAssume = null;
		Expression suchThat = null;
		Attributes attrs = null;
		IToken endTok;
		
		if (la.kind == 64) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(68);
		if (!isGhost) { x = t; } 
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		LocalIdentTypeOptional(out d, isGhost);
		lhss.Add(d); d.Attributes = attrs; attrs = null; 
		while (la.kind == 20) {
			Get();
			while (la.kind == 38) {
				Attribute(ref attrs);
			}
			LocalIdentTypeOptional(out d, isGhost);
			lhss.Add(d); d.Attributes = attrs; attrs = null; 
		}
		if (la.kind == 89 || la.kind == 91) {
			if (la.kind == 89) {
				Get();
				assignTok = t;
				lhs0 = new IdentifierExpr(lhss[0].Tok, lhss[0].Name);
				
				Rhs(out r, lhs0);
				rhss.Add(r); 
				while (la.kind == 20) {
					Get();
					Rhs(out r, lhs0);
					rhss.Add(r); 
				}
			} else {
				Get();
				assignTok = t; 
				if (la.kind == _assume) {
					Expect(28);
					suchThatAssume = t; 
				}
				Expression(out suchThat, false, true);
			}
		}
		while (!(la.kind == 0 || la.kind == 25)) {SynErr(179); Get();}
		Expect(25);
		endTok = t; 
		ConcreteUpdateStatement update;
		if (suchThat != null) {
		 var ies = new List<Expression>();
		 foreach (var lhs in lhss) {
		   ies.Add(new IdentifierExpr(lhs.Tok, lhs.Name));
		 }
		 update = new AssignSuchThatStmt(assignTok, endTok, ies, suchThat, suchThatAssume);
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
		
	}

	void IfStmt(out Statement/*!*/ ifStmt) {
		Contract.Ensures(Contract.ValueAtReturn(out ifStmt) != null); IToken/*!*/ x;
		Expression guard = null;  IToken guardEllipsis = null;
		BlockStmt/*!*/ thn;
		BlockStmt/*!*/ bs;
		Statement/*!*/ s;
		Statement els = null;
		IToken bodyStart, bodyEnd, endTok;
		List<GuardedAlternative> alternatives;
		ifStmt = dummyStmt;  // to please the compiler
		
		Expect(93);
		x = t; 
		if (IsAlternative()) {
			AlternativeBlock(out alternatives, out endTok);
			ifStmt = new AlternativeStmt(x, endTok, alternatives); 
		} else if (StartOf(20)) {
			if (StartOf(21)) {
				Guard(out guard);
			} else {
				Get();
				guardEllipsis = t; 
			}
			BlockStmt(out thn, out bodyStart, out bodyEnd);
			endTok = thn.EndTok; 
			if (la.kind == 32) {
				Get();
				if (la.kind == 93) {
					IfStmt(out s);
					els = s; endTok = s.EndTok; 
				} else if (la.kind == 38) {
					BlockStmt(out bs, out bodyStart, out bodyEnd);
					els = bs; endTok = bs.EndTok; 
				} else SynErr(180);
			}
			if (guardEllipsis != null) {
			 ifStmt = new SkeletonStatement(new IfStmt(x, endTok, guard, thn, els), guardEllipsis, null);
			} else {
			 ifStmt = new IfStmt(x, endTok, guard, thn, els);
			}
			
		} else SynErr(181);
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
		
		Expect(94);
		x = t; 
		if (IsLoopSpec() || IsAlternative()) {
			while (StartOf(22)) {
				LoopSpec(invariants, decreases, ref mod, ref decAttrs, ref modAttrs);
			}
			AlternativeBlock(out alternatives, out endTok);
			stmt = new AlternativeLoopStmt(x, endTok, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(mod, modAttrs), alternatives); 
		} else if (StartOf(20)) {
			if (StartOf(21)) {
				Guard(out guard);
				Contract.Assume(guard == null || cce.Owner.None(guard)); 
			} else {
				Get();
				guardEllipsis = t; 
			}
			while (StartOf(22)) {
				LoopSpec(invariants, decreases, ref mod, ref decAttrs, ref modAttrs);
			}
			if (la.kind == _lbrace) {
				BlockStmt(out body, out bodyStart, out bodyEnd);
				endTok = body.EndTok; isDirtyLoop = false; 
			} else if (la.kind == _ellipsis) {
				Expect(51);
				bodyEllipsis = t; endTok = t; isDirtyLoop = false; 
			} else if (StartOf(23)) {
			} else SynErr(182);
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
			
		} else SynErr(183);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(95);
		x = t; 
		Expression(out e, true, true);
		if (la.kind == _lbrace) {
			Expect(38);
			usesOptionalBrace = true; 
			while (la.kind == 30) {
				CaseStatement(out c);
				cases.Add(c); 
			}
			Expect(39);
		} else if (StartOf(23)) {
			while (la.kind == _case) {
				CaseStatement(out c);
				cases.Add(c); 
			}
		} else SynErr(184);
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
		
		if (la.kind == 98) {
			Get();
			x = t; tok = x; 
		} else if (la.kind == 99) {
			Get();
			x = t;
			errors.Warning(t, "the 'parallel' keyword has been deprecated; the comprehension statement now uses the keyword 'forall' (and the parentheses around the bound variables are now optional)");
			
		} else SynErr(185);
		if (la.kind == _openparen) {
			Expect(42);
			if (la.kind == 1) {
				QuantifierDomain(out bvars, out attrs, out range);
			}
			Expect(43);
		} else if (StartOf(24)) {
			if (la.kind == _ident) {
				QuantifierDomain(out bvars, out attrs, out range);
			}
		} else SynErr(186);
		if (bvars == null) { bvars = new List<BoundVar>(); }
		if (range == null) { range = new LiteralExpr(x, true); }
		
		while (la.kind == 79 || la.kind == 80) {
			isFree = false; 
			if (la.kind == 79) {
				Get();
				isFree = true;
				errors.Warning(t, "the 'free' keyword is soon to be deprecated");
				
			}
			Expect(80);
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
		CalcStmt.CalcOp op, calcOp = Microsoft.Dafny.CalcStmt.DefaultOp, resOp = Microsoft.Dafny.CalcStmt.DefaultOp;
		var lines = new List<Expression>();
		var hints = new List<BlockStmt>();
		CalcStmt.CalcOp stepOp;
		var stepOps = new List<CalcStmt.CalcOp>();
		CalcStmt.CalcOp maybeOp;
		Expression e;
		IToken opTok;
		IToken danglingOperator = null;
		
		Expect(29);
		x = t; 
		if (StartOf(25)) {
			CalcOp(out opTok, out calcOp);
			maybeOp = calcOp.ResultOp(calcOp); // guard against non-transitive calcOp (like !=)
			if (maybeOp == null) {
			 SemErr(opTok, "the main operator of a calculation must be transitive");
			}
			resOp = calcOp;
			
		}
		Expect(38);
		while (StartOf(7)) {
			Expression(out e, false, true);
			lines.Add(e); stepOp = calcOp; danglingOperator = null; 
			Expect(25);
			if (StartOf(25)) {
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
				if (la.kind == 38) {
					BlockStmt(out subBlock, out t0, out t1);
					hintEnd = subBlock.EndTok; subhints.Add(subBlock); 
				} else if (la.kind == 29) {
					CalcStmt(out subCalc);
					hintEnd = subCalc.EndTok; subhints.Add(subCalc); 
				} else SynErr(187);
			}
			var h = new BlockStmt(hintStart, hintEnd, subhints); // if the hint is empty, hintStart is the first token of the next line, but it doesn't matter because the block statement is just used as a container
			hints.Add(h);
			if (h.Body.Count != 0) { danglingOperator = null; }
			
		}
		Expect(39);
		if (danglingOperator != null) {
		 SemErr(danglingOperator, "a calculation cannot end with an operator");
		}
		if (lines.Count > 0) {
		 // Repeat the last line to create a dummy line for the dangling hint
		 lines.Add(lines[lines.Count - 1]);
		}
		s = new CalcStmt(x, t, calcOp, lines, hints, stepOps, resOp);
		
	}

	void ModifyStmt(out Statement s) {
		IToken tok;  IToken endTok = Token.NoToken;
		Attributes attrs = null;
		FrameExpression fe;  var mod = new List<FrameExpression>();
		BlockStmt body = null;  IToken bodyStart;
		IToken ellipsisToken = null;
		
		Expect(100);
		tok = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(18)) {
			FrameExpression(out fe, false, true);
			mod.Add(fe); 
			while (la.kind == 20) {
				Get();
				FrameExpression(out fe, false, true);
				mod.Add(fe); 
			}
		} else if (la.kind == 51) {
			Get();
			ellipsisToken = t; 
		} else SynErr(188);
		if (la.kind == 38) {
			BlockStmt(out body, out bodyStart, out endTok);
		} else if (la.kind == 25) {
			while (!(la.kind == 0 || la.kind == 25)) {SynErr(189); Get();}
			Get();
			endTok = t; 
		} else SynErr(190);
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
		
		if (la.kind == 90) {
			Get();
			returnTok = t; 
		} else if (la.kind == 81) {
			Get();
			returnTok = t; isYield = true; 
		} else SynErr(191);
		if (StartOf(26)) {
			Rhs(out r, null);
			rhss = new List<AssignmentRhs>(); rhss.Add(r); 
			while (la.kind == 20) {
				Get();
				Rhs(out r, null);
				rhss.Add(r); 
			}
		}
		Expect(25);
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
		Expect(51);
		dotdotdot = t; 
		if (la.kind == 88) {
			Get();
			names = new List<IToken>(); exprs = new List<Expression>(); whereTok = t;
			Ident(out tok);
			names.Add(tok); 
			while (la.kind == 20) {
				Get();
				Ident(out tok);
				names.Add(tok); 
			}
			Expect(89);
			Expression(out e, false, true);
			exprs.Add(e); 
			while (la.kind == 20) {
				Get();
				Expression(out e, false, true);
				exprs.Add(e); 
			}
			if (exprs.Count != names.Count) {
			 SemErr(whereTok, exprs.Count < names.Count ? "not enough expressions" : "too many expressions");
			 names = null; exprs = null;
			}
			
		}
		Expect(25);
		s = new SkeletonStatement(dotdotdot, t, names, exprs); 
	}

	void Rhs(out AssignmentRhs r, Expression receiverForInitCall) {
		Contract.Ensures(Contract.ValueAtReturn<AssignmentRhs>(out r) != null);
		IToken/*!*/ x, newToken;  Expression/*!*/ e;
		Type ty = null;
		List<Expression> ee = null;
		List<Expression> args = null;
		r = dummyRhs;  // to please compiler
		Attributes attrs = null;
		
		if (la.kind == 92) {
			Get();
			newToken = t; 
			TypeAndToken(out x, out ty);
			if (la.kind == 24 || la.kind == 40 || la.kind == 42) {
				if (la.kind == 40) {
					Get();
					ee = new List<Expression>(); 
					Expressions(ee);
					Expect(41);
					var tmp = theBuiltIns.ArrayType(ee.Count, new IntType(), true);
					
				} else {
					x = null; args = new List<Expression/*!*/>(); 
					if (la.kind == 24) {
						Get();
						Ident(out x);
					}
					Expect(42);
					if (StartOf(7)) {
						Expressions(args);
					}
					Expect(43);
				}
			}
			if (ee != null) {
			 r = new TypeRhs(newToken, ty, ee);
			} else if (args != null) {
			 r = new TypeRhs(newToken, ty, x == null ? null : x.val, receiverForInitCall, args);
			} else {
			 r = new TypeRhs(newToken, ty);
			}
			
		} else if (la.kind == 49) {
			Get();
			r = new HavocRhs(t); 
		} else if (StartOf(7)) {
			Expression(out e, false, true);
			r = new ExprRhs(e); 
		} else SynErr(192);
		while (la.kind == 38) {
			Attribute(ref attrs);
		}
		r.Attributes = attrs; 
	}

	void Lhs(out Expression e) {
		e = dummyExpr;  // the assignment is to please the compiler, the dummy value to satisfy contracts in the event of a parse error
		
		if (la.kind == 1) {
			NameSegment(out e);
			while (la.kind == 24 || la.kind == 40 || la.kind == 42) {
				Suffix(ref e);
			}
		} else if (StartOf(27)) {
			ConstAtomExpression(out e, false, false);
			Suffix(ref e);
			while (la.kind == 24 || la.kind == 40 || la.kind == 42) {
				Suffix(ref e);
			}
		} else SynErr(193);
	}

	void Expressions(List<Expression> args) {
		Expression e; 
		Expression(out e, true, true);
		args.Add(e); 
		while (la.kind == 20) {
			Get();
			Expression(out e, true, true);
			args.Add(e); 
		}
	}

	void AlternativeBlock(out List<GuardedAlternative> alternatives, out IToken endTok) {
		alternatives = new List<GuardedAlternative>();
		IToken x;
		Expression e;
		List<Statement> body;
		
		Expect(38);
		while (la.kind == 30) {
			Get();
			x = t; 
			Expression(out e, true, false);
			Expect(26);
			body = new List<Statement>(); 
			while (StartOf(15)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, e, body)); 
		}
		Expect(39);
		endTok = t; 
	}

	void Guard(out Expression e) {
		Expression/*!*/ ee;  e = null; 
		if (la.kind == 49) {
			Get();
			e = null; 
		} else if (IsParenStar()) {
			Expect(42);
			Expect(49);
			Expect(43);
			e = null; 
		} else if (StartOf(7)) {
			Expression(out ee, true, true);
			e = ee; 
		} else SynErr(194);
	}

	void LoopSpec(List<MaybeFreeExpression> invariants, List<Expression> decreases, ref List<FrameExpression> mod, ref Attributes decAttrs, ref Attributes modAttrs) {
		Expression e; FrameExpression fe;
		bool isFree = false; Attributes attrs = null;
		
		if (la.kind == 34 || la.kind == 79) {
			while (!(la.kind == 0 || la.kind == 34 || la.kind == 79)) {SynErr(195); Get();}
			if (la.kind == 79) {
				Get();
				isFree = true; errors.Warning(t, "the 'free' keyword is soon to be deprecated"); 
			}
			Expect(34);
			while (IsAttribute()) {
				Attribute(ref attrs);
			}
			Expression(out e, false, true);
			invariants.Add(new MaybeFreeExpression(e, isFree, attrs)); 
			OldSemi();
		} else if (la.kind == 33) {
			while (!(la.kind == 0 || la.kind == 33)) {SynErr(196); Get();}
			Get();
			while (IsAttribute()) {
				Attribute(ref decAttrs);
			}
			DecreasesList(decreases, true, true);
			OldSemi();
		} else if (la.kind == 35) {
			while (!(la.kind == 0 || la.kind == 35)) {SynErr(197); Get();}
			Get();
			mod = mod ?? new List<FrameExpression>(); 
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			FrameExpression(out fe, false, true);
			mod.Add(fe); 
			while (la.kind == 20) {
				Get();
				FrameExpression(out fe, false, true);
				mod.Add(fe); 
			}
			OldSemi();
		} else SynErr(198);
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(30);
		x = t; 
		Ident(out id);
		if (la.kind == 42) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 20) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(43);
		}
		Expect(26);
		while (!(StartOf(28))) {SynErr(199); Get();}
		while (IsNotEndOfCase()) {
			Stmt(body);
			while (!(StartOf(28))) {SynErr(200); Get();}
		}
		c = new MatchCaseStmt(x, id.val, arguments, body); 
	}

	void QuantifierDomain(out List<BoundVar> bvars, out Attributes attrs, out Expression range) {
		bvars = new List<BoundVar>();
		BoundVar/*!*/ bv;
		attrs = null;
		range = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 20) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (la.kind == _verticalbar) {
			Expect(21);
			Expression(out range, true, true);
		}
	}

	void CalcOp(out IToken x, out CalcStmt.CalcOp/*!*/ op) {
		var binOp = BinaryExpr.Opcode.Eq; // Returns Eq if parsing fails because it is compatible with any other operator
		Expression k = null;
		x = null;
		
		switch (la.kind) {
		case 46: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Eq; 
			if (la.kind == 101) {
				Get();
				Expect(40);
				Expression(out k, true, true);
				Expect(41);
			}
			break;
		}
		case 44: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 45: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 102: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 103: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 47: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 48: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 104: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 105: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 106: case 107: {
			EquivOp();
			x = t;  binOp = BinaryExpr.Opcode.Iff; 
			break;
		}
		case 108: case 109: {
			ImpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Imp; 
			break;
		}
		case 110: case 111: {
			ExpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Exp; 
			break;
		}
		default: SynErr(201); break;
		}
		if (k == null) {
		 op = new Microsoft.Dafny.CalcStmt.BinaryCalcOp(binOp);
		} else {
		 op = new Microsoft.Dafny.CalcStmt.TernaryCalcOp(k);
		}
		
	}

	void EquivOp() {
		if (la.kind == 106) {
			Get();
		} else if (la.kind == 107) {
			Get();
		} else SynErr(202);
	}

	void ImpliesOp() {
		if (la.kind == 108) {
			Get();
		} else if (la.kind == 109) {
			Get();
		} else SynErr(203);
	}

	void ExpliesOp() {
		if (la.kind == 110) {
			Get();
		} else if (la.kind == 111) {
			Get();
		} else SynErr(204);
	}

	void AndOp() {
		if (la.kind == 112) {
			Get();
		} else if (la.kind == 113) {
			Get();
		} else SynErr(205);
	}

	void OrOp() {
		if (la.kind == 114) {
			Get();
		} else if (la.kind == 115) {
			Get();
		} else SynErr(206);
	}

	void NegOp() {
		if (la.kind == 116) {
			Get();
		} else if (la.kind == 117) {
			Get();
		} else SynErr(207);
	}

	void Forall() {
		if (la.kind == 98) {
			Get();
		} else if (la.kind == 118) {
			Get();
		} else SynErr(208);
	}

	void Exists() {
		if (la.kind == 119) {
			Get();
		} else if (la.kind == 120) {
			Get();
		} else SynErr(209);
	}

	void QSep() {
		if (la.kind == 22) {
			Get();
		} else if (la.kind == 23) {
			Get();
		} else SynErr(210);
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
			if (la.kind == 108 || la.kind == 109) {
				ImpliesOp();
				x = t; 
				ImpliesExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
			} else if (la.kind == 110 || la.kind == 111) {
				ExpliesOp();
				x = t; 
				LogicalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e0, e1); 
				while (IsExpliesOp()) {
					ExpliesOp();
					x = t; 
					LogicalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e0, e1); 
				}
			} else SynErr(211);
		}
	}

	void LogicalExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0, allowSemi, allowLambda);
		if (IsAndOp() || IsOrOp()) {
			if (la.kind == 112 || la.kind == 113) {
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
			} else if (la.kind == 114 || la.kind == 115) {
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
			} else SynErr(212);
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
		case 46: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			if (la.kind == 101) {
				Get();
				Expect(40);
				Expression(out k, true, true);
				Expect(41);
			}
			break;
		}
		case 44: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 45: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 102: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 103: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 47: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			if (la.kind == 101) {
				Get();
				Expect(40);
				Expression(out k, true, true);
				Expect(41);
			}
			break;
		}
		case 121: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 50: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 116: {
			Get();
			x = t;  y = Token.NoToken; 
			if (la.val == "!") {
				Expect(116);
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
		case 48: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 104: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 105: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(213); break;
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
		if (la.kind == 122) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 123) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(214);
	}

	void UnaryExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		if (la.kind == 123) {
			Get();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new NegationExpression(x, e); 
		} else if (la.kind == 116 || la.kind == 117) {
			NegOp();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Not, e); 
		} else if (IsMapDisplay()) {
			Expect(16);
			x = t; 
			MapDisplayExpr(x, out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (IsLambda(allowLambda)) {
			LambdaExpression(out e, allowSemi);
		} else if (StartOf(29)) {
			EndlessExpression(out e, allowSemi, allowLambda);
		} else if (la.kind == 1) {
			NameSegment(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (la.kind == 38 || la.kind == 40) {
			DisplayExpr(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (la.kind == 14) {
			MultiSetExpr(out e);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else if (StartOf(27)) {
			ConstAtomExpression(out e, allowSemi, allowLambda);
			while (IsSuffix()) {
				Suffix(ref e);
			}
		} else SynErr(215);
	}

	void MulOp(out IToken x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 49) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 124) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 125) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(216);
	}

	void MapDisplayExpr(IToken/*!*/ mapToken, out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		List<ExpressionPair/*!*/>/*!*/ elements= new List<ExpressionPair/*!*/>() ;
		e = dummyExpr;
		
		Expect(40);
		if (StartOf(7)) {
			MapLiteralExpressions(out elements);
		}
		e = new MapDisplayExpr(mapToken, elements);
		Expect(41);
	}

	void Suffix(ref Expression e) {
		Contract.Requires(e != null); Contract.Ensures(e!=null);
		IToken id, x;
		Expression e0 = null;  Expression e1 = null;  Expression ee;  bool anyDots = false;
		List<Expression> multipleLengths = null; bool takeRest = false; // takeRest is relevant only if multipleLengths is non-null
		List<Expression> multipleIndices = null;
		
		if (la.kind == 24) {
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
			} else if (la.kind == 101) {
				HashCall(id, out openParen, out typeArgs, out args);
			} else if (StartOf(30)) {
			} else SynErr(217);
			e = new ExprDotName(id, e, id.val, typeArgs);
			if (openParen != null) {
			 e = new ApplySuffix(openParen, e, args);
			}
			
		} else if (la.kind == 40) {
			Get();
			x = t; 
			if (StartOf(7)) {
				Expression(out ee, true, true);
				e0 = ee; 
				if (la.kind == 132) {
					Get();
					anyDots = true; 
					if (StartOf(7)) {
						Expression(out ee, true, true);
						e1 = ee; 
					}
				} else if (la.kind == 89) {
					Get();
					Expression(out ee, true, true);
					e1 = ee; 
				} else if (la.kind == 19) {
					Get();
					multipleLengths = new List<Expression>();
					multipleLengths.Add(e0);  // account for the Expression read before the colon
					takeRest = true;
					
					if (StartOf(7)) {
						Expression(out ee, true, true);
						multipleLengths.Add(ee); takeRest = false; 
						while (IsNonFinalColon()) {
							Expect(19);
							Expression(out ee, true, true);
							multipleLengths.Add(ee); 
						}
						if (la.kind == 19) {
							Get();
							takeRest = true; 
						}
					}
				} else if (la.kind == 20 || la.kind == 41) {
					while (la.kind == 20) {
						Get();
						Expression(out ee, true, true);
						if (multipleIndices == null) {
						 multipleIndices = new List<Expression>();
						 multipleIndices.Add(e0);
						}
						multipleIndices.Add(ee);
						
					}
				} else SynErr(218);
			} else if (la.kind == 132) {
				Get();
				anyDots = true; 
				if (StartOf(7)) {
					Expression(out ee, true, true);
					e1 = ee; 
				}
			} else SynErr(219);
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
			
			Expect(41);
		} else if (la.kind == 42) {
			Get();
			IToken openParen = t; var args = new List<Expression>(); 
			if (StartOf(7)) {
				Expressions(args);
			}
			Expect(43);
			e = new ApplySuffix(openParen, e, args); 
		} else SynErr(220);
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
		} else if (la.kind == 42) {
			Get();
			x = t; 
			if (la.kind == 1) {
				IdentTypeOptional(out bv);
				bvs.Add(bv); 
				while (la.kind == 20) {
					Get();
					IdentTypeOptional(out bv);
					bvs.Add(bv); 
				}
			}
			Expect(43);
		} else SynErr(221);
		while (la.kind == 36 || la.kind == 37) {
			if (la.kind == 36) {
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
		e = dummyExpr;
		
		switch (la.kind) {
		case 93: {
			Get();
			x = t; 
			Expression(out e, true, true);
			Expect(31);
			Expression(out e0, true, true);
			Expect(32);
			Expression(out e1, allowSemi, allowLambda);
			e = new ITEExpr(x, e, e0, e1); 
			break;
		}
		case 95: {
			MatchExpression(out e, allowSemi, allowLambda);
			break;
		}
		case 98: case 118: case 119: case 120: {
			QuantifierGuts(out e, allowSemi, allowLambda);
			break;
		}
		case 13: {
			SetComprehensionExpr(out e, allowSemi, allowLambda);
			break;
		}
		case 28: case 29: case 96: {
			StmtInExpr(out s);
			Expression(out e, allowSemi, allowLambda);
			e = new StmtExpr(s.Tok, s, e); 
			break;
		}
		case 64: case 68: {
			LetExpr(out e, allowSemi, allowLambda);
			break;
		}
		case 16: {
			Get();
			x = t; 
			MapComprehensionExpr(x, out e, allowSemi, allowLambda);
			break;
		}
		case 86: {
			NamedExpr(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(222); break;
		}
	}

	void NameSegment(out Expression e) {
		IToken id;
		IToken openParen = null;  List<Type> typeArgs = null;  List<Expression> args = null;
		
		Ident(out id);
		if (IsGenericInstantiation()) {
			typeArgs = new List<Type>(); 
			GenericInstantiation(typeArgs);
		} else if (la.kind == 101) {
			HashCall(id, out openParen, out typeArgs, out args);
		} else if (StartOf(30)) {
		} else SynErr(223);
		e = new NameSegment(id, id.val, typeArgs);
		if (openParen != null) {
		 e = new ApplySuffix(openParen, e, args);
		}
		
	}

	void DisplayExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken x;  List<Expression> elements;
		e = dummyExpr;
		
		if (la.kind == 38) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(7)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements);
			Expect(39);
		} else if (la.kind == 40) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(7)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(41);
		} else SynErr(224);
	}

	void MultiSetExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		Expect(14);
		x = t; 
		if (la.kind == 38) {
			Get();
			elements = new List<Expression/*!*/>(); 
			if (StartOf(7)) {
				Expressions(elements);
			}
			e = new MultiSetDisplayExpr(x, elements);
			Expect(39);
		} else if (la.kind == 42) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			Expression(out e, true, true);
			e = new MultiSetFormingExpr(x, e); 
			Expect(43);
		} else SynErr(225);
	}

	void ConstAtomExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;   Basetypes.BigDec d;
		e = dummyExpr;  Type toType = null;
		
		switch (la.kind) {
		case 126: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 127: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 128: {
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
		case 17: {
			Get();
			e = new CharLiteralExpr(t, t.val.Substring(1, t.val.Length - 2)); 
			break;
		}
		case 18: {
			Get();
			bool isVerbatimString;
			string s = Util.RemoveParsedStringQuotes(t.val, out isVerbatimString);
			e = new StringLiteralExpr(t, s, isVerbatimString);
			
			break;
		}
		case 129: {
			Get();
			e = new ThisExpr(t); 
			break;
		}
		case 130: {
			Get();
			x = t; 
			Expect(42);
			Expression(out e, true, true);
			Expect(43);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Fresh, e); 
			break;
		}
		case 131: {
			Get();
			x = t; 
			Expect(42);
			Expression(out e, true, true);
			Expect(43);
			e = new OldExpr(x, e); 
			break;
		}
		case 21: {
			Get();
			x = t; 
			Expression(out e, true, true);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Cardinality, e); 
			Expect(21);
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
			Expect(42);
			Expression(out e, true, true);
			Expect(43);
			e = new ConversionExpr(x, e, toType); 
			break;
		}
		case 42: {
			ParensExpression(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(226); break;
		}
	}

	void Nat(out BigInteger n) {
		n = BigInteger.Zero;
		string S;
		
		if (la.kind == 2) {
			Get();
			S = Util.RemoveUnderscores(t.val);
			try {
			 n = BigInteger.Parse(S);
			} catch (System.FormatException) {
			 SemErr("incorrectly formatted number");
			 n = BigInteger.Zero;
			}
			
		} else if (la.kind == 3) {
			Get();
			S = Util.RemoveUnderscores(t.val.Substring(2));
			try {
			 // note: leading 0 required when parsing positive hex numbers
			 n = BigInteger.Parse("0" + S, System.Globalization.NumberStyles.HexNumber);
			} catch (System.FormatException) {
			 SemErr("incorrectly formatted number");
			 n = BigInteger.Zero;
			}
			
		} else SynErr(227);
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
		
		Expect(42);
		x = t; 
		if (StartOf(7)) {
			Expressions(args);
		}
		Expect(43);
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
		if (la.kind == 26) {
			Get();
			oneShot = false; 
		} else if (la.kind == 27) {
			Get();
			oneShot = true; 
		} else SynErr(228);
	}

	void MapLiteralExpressions(out List<ExpressionPair> elements) {
		Expression/*!*/ d, r;
		elements = new List<ExpressionPair/*!*/>(); 
		Expression(out d, true, true);
		Expect(89);
		Expression(out r, true, true);
		elements.Add(new ExpressionPair(d,r)); 
		while (la.kind == 20) {
			Get();
			Expression(out d, true, true);
			Expect(89);
			Expression(out r, true, true);
			elements.Add(new ExpressionPair(d,r)); 
		}
	}

	void MapComprehensionExpr(IToken mapToken, out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		BoundVar bv;
		List<BoundVar> bvars = new List<BoundVar>();
		Expression range = null;
		Expression body;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		if (la.kind == 21) {
			Get();
			Expression(out range, true, true);
		}
		QSep();
		Expression(out body, allowSemi, allowLambda);
		e = new MapComprehension(mapToken, bvars, range ?? new LiteralExpr(mapToken, true), body);
		
	}

	void MatchExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  MatchCaseExpr/*!*/ c;
		List<MatchCaseExpr/*!*/> cases = new List<MatchCaseExpr/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(95);
		x = t; 
		Expression(out e, allowSemi, allowLambda);
		if (la.kind == _lbrace) {
			Expect(38);
			usesOptionalBrace = true; 
			while (la.kind == 30) {
				CaseExpression(out c, true, true);
				cases.Add(c); 
			}
			Expect(39);
		} else if (StartOf(31)) {
			while (la.kind == _case) {
				CaseExpression(out c, allowSemi, allowLambda);
				cases.Add(c); 
			}
		} else SynErr(229);
		e = new MatchExpr(x, e, cases, usesOptionalBrace); 
	}

	void QuantifierGuts(out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		List<BoundVar/*!*/> bvars;
		Attributes attrs;
		Expression range;
		Expression/*!*/ body;
		
		if (la.kind == 98 || la.kind == 118) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 119 || la.kind == 120) {
			Exists();
			x = t; 
		} else SynErr(230);
		QuantifierDomain(out bvars, out attrs, out range);
		QSep();
		Expression(out body, allowSemi, allowLambda);
		if (univ) {
		 q = new ForallExpr(x, bvars, range, body, attrs);
		} else {
		 q = new ExistsExpr(x, bvars, range, body, attrs);
		}
		
	}

	void SetComprehensionExpr(out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null);
		IToken x = Token.NoToken;
		BoundVar bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar>();
		Expression range;
		Expression body = null;
		
		Expect(13);
		x = t; 
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 20) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		Expect(21);
		Expression(out range, allowSemi, allowLambda);
		if (IsQSep()) {
			QSep();
			Expression(out body, allowSemi, allowLambda);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(x, bvars, range, body);
		
	}

	void StmtInExpr(out Statement s) {
		s = dummyStmt; 
		if (la.kind == 96) {
			AssertStmt(out s);
		} else if (la.kind == 28) {
			AssumeStmt(out s);
		} else if (la.kind == 29) {
			CalcStmt(out s);
		} else SynErr(231);
	}

	void LetExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken x = null;
		bool isGhost = false;
		var letLHSs = new List<CasePattern>();
		var letRHSs = new List<Expression>();
		CasePattern pat;
		bool exact = true;
		e = dummyExpr;
		
		if (la.kind == 64) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(68);
		if (!isGhost) { x = t; } 
		CasePattern(out pat);
		if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
		letLHSs.Add(pat);
		
		while (la.kind == 20) {
			Get();
			CasePattern(out pat);
			if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
			letLHSs.Add(pat);
			
		}
		if (la.kind == 89) {
			Get();
		} else if (la.kind == 91) {
			Get();
			exact = false;
			foreach (var lhs in letLHSs) {
			 if (lhs.Arguments != null) {
			   SemErr(lhs.tok, "LHS of let-such-that expression must be variables, not general patterns");
			 }
			}
			
		} else SynErr(232);
		Expression(out e, false, true);
		letRHSs.Add(e); 
		while (la.kind == 20) {
			Get();
			Expression(out e, false, true);
			letRHSs.Add(e); 
		}
		Expect(25);
		Expression(out e, allowSemi, allowLambda);
		e = new LetExpr(x, letLHSs, letRHSs, e, exact); 
	}

	void NamedExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken/*!*/ x, d;
		e = dummyExpr;
		Expression expr;
		
		Expect(86);
		x = t; 
		NoUSIdent(out d);
		Expect(19);
		Expression(out e, allowSemi, allowLambda);
		expr = e;
		e = new NamedExpr(x, d.val, expr); 
	}

	void CasePattern(out CasePattern pat) {
		IToken id;  List<CasePattern> arguments;
		BoundVar bv;
		pat = null;
		
		if (IsIdentParen()) {
			Ident(out id);
			Expect(42);
			arguments = new List<CasePattern>(); 
			if (la.kind == 1) {
				CasePattern(out pat);
				arguments.Add(pat); 
				while (la.kind == 20) {
					Get();
					CasePattern(out pat);
					arguments.Add(pat); 
				}
			}
			Expect(43);
			pat = new CasePattern(id, id.val, arguments); 
		} else if (la.kind == 1) {
			IdentTypeOptional(out bv);
			pat = new CasePattern(bv.tok, bv);
			
		} else SynErr(233);
		if (pat == null) {
		 pat = new CasePattern(t, "_ParseError", new List<CasePattern>());
		}
		
	}

	void CaseExpression(out MatchCaseExpr c, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		Expression/*!*/ body;
		
		Expect(30);
		x = t; 
		Ident(out id);
		if (la.kind == 42) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 20) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(43);
		}
		Expect(26);
		Expression(out body, allowSemi, allowLambda);
		c = new MatchCaseExpr(x, id.val, arguments, body); 
	}

	void HashCall(IToken id, out IToken openParen, out List<Type> typeArgs, out List<Expression> args) {
		Expression k; args = new List<Expression>(); typeArgs = null; 
		Expect(101);
		id.val = id.val + "#"; 
		if (la.kind == 44) {
			typeArgs = new List<Type>(); 
			GenericInstantiation(typeArgs);
		}
		Expect(40);
		Expression(out k, true, true);
		Expect(41);
		args.Add(k); 
		Expect(42);
		openParen = t; 
		if (StartOf(7)) {
			Expressions(args);
		}
		Expect(43);
	}

	void DotSuffix(out IToken x, out IToken y) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		x = Token.NoToken;
		y = null;
		
		Expect(24);
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
			
		} else if (la.kind == 37) {
			Get();
			x = t; 
		} else if (la.kind == 36) {
			Get();
			x = t; 
		} else SynErr(234);
	}



	public void Parse() {
		la = new Token();
		la.val = "";
		Get();
		Dafny();
		Expect(0);

		Expect(0);
	}

	static readonly bool[,]/*!*/ set = {
		{T,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,T,x,x, T,T,T,x, x,T,T,T, T,T,T,T, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,T, T,x,T,T, T,x,x,T, x,x,T,T, T,T,T,T, T,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, T,x,x,x, x,T,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,T,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, T,x,x,x, x,x,T,T, T,T,T,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,x,x, x,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, T,x,x,x, x,x,x,x, x,T,T,x, T,x,T,x, x,T,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,T,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,T,T,x, T,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,T, x,x,T,T, T,T,T,T, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,T, x,x,T,x, T,x,x,x, x,x,x,x, x,T,T,x, T,x,x,x, x,T,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,T,x, T,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,T,T,x, T,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,T, x,x,T,T, T,T,T,T, x,x,x},
		{T,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,T,T,x, T,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, T,x,T,x, x,x,x,x, x,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,T, x,x,T,T, T,T,T,T, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,T,T,x, T,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, T,x,T,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,T, x,x,T,T, T,T,T,T, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, T,T,T,x, x,x,x,x, x,x,T,T, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, T,T,T,x, x,x,x,x, x,x,T,T, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,x,x, T,x,T,x, x,T,T,x, T,T,T,x, x,T,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,T,x, T,x,T,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, T,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,T, x,x,T,T, T,T,T,T, x,x,x},
		{x,x,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{T,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, T,T,T,x, x,x,x,x, x,x,T,T, x,x,T,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,T,x,T, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, x,T,T,x, T,x,x,x, x,T,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, x,T,T,T, x,T,T,T, T,T,T,T, T,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,T,T,T, T,T,T,T, T,T,T,T, T,x,x},
		{T,T,T,T, T,x,x,x, T,x,T,x, x,x,x,x, x,T,T,T, T,T,T,T, x,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, x,T,T,T, T,T,T,T, T,T,T,T, x,T,T,x, T,x,x,x, x,T,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, x,T,T,x, x,T,T,T, T,T,T,T, T,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,T,T,T, T,T,T,T, T,T,T,T, T,x,x}

	};
} // end Parser


public class Errors {
	public int count = 0;                                    // number of errors detected
	public System.IO.TextWriter/*!*/ errorStream = Console.Out;   // error messages go to this stream
	public string errMsgFormat = "{0}({1},{2}): error: {3}"; // 0=filename, 1=line, 2=column, 3=text
	public string warningMsgFormat = "{0}({1},{2}): warning: {3}"; // 0=filename, 1=line, 2=column, 3=text

	public void SynErr(string filename, int line, int col, int n) {
		SynErr(filename, line, col, GetSyntaxErrorString(n));
	}

	public virtual void SynErr(string filename, int line, int col, string/*!*/ msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(errMsgFormat, filename, line, col, msg);
		count++;
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
			case 14: s = "multiset expected"; break;
			case 15: s = "seq expected"; break;
			case 16: s = "map expected"; break;
			case 17: s = "charToken expected"; break;
			case 18: s = "stringToken expected"; break;
			case 19: s = "colon expected"; break;
			case 20: s = "comma expected"; break;
			case 21: s = "verticalbar expected"; break;
			case 22: s = "doublecolon expected"; break;
			case 23: s = "bullet expected"; break;
			case 24: s = "dot expected"; break;
			case 25: s = "semi expected"; break;
			case 26: s = "darrow expected"; break;
			case 27: s = "arrow expected"; break;
			case 28: s = "assume expected"; break;
			case 29: s = "calc expected"; break;
			case 30: s = "case expected"; break;
			case 31: s = "then expected"; break;
			case 32: s = "else expected"; break;
			case 33: s = "decreases expected"; break;
			case 34: s = "invariant expected"; break;
			case 35: s = "modifies expected"; break;
			case 36: s = "reads expected"; break;
			case 37: s = "requires expected"; break;
			case 38: s = "lbrace expected"; break;
			case 39: s = "rbrace expected"; break;
			case 40: s = "lbracket expected"; break;
			case 41: s = "rbracket expected"; break;
			case 42: s = "openparen expected"; break;
			case 43: s = "closeparen expected"; break;
			case 44: s = "openAngleBracket expected"; break;
			case 45: s = "closeAngleBracket expected"; break;
			case 46: s = "eq expected"; break;
			case 47: s = "neq expected"; break;
			case 48: s = "neqAlt expected"; break;
			case 49: s = "star expected"; break;
			case 50: s = "notIn expected"; break;
			case 51: s = "ellipsis expected"; break;
			case 52: s = "\"include\" expected"; break;
			case 53: s = "\"abstract\" expected"; break;
			case 54: s = "\"module\" expected"; break;
			case 55: s = "\"refines\" expected"; break;
			case 56: s = "\"import\" expected"; break;
			case 57: s = "\"opened\" expected"; break;
			case 58: s = "\"=\" expected"; break;
			case 59: s = "\"as\" expected"; break;
			case 60: s = "\"default\" expected"; break;
			case 61: s = "\"class\" expected"; break;
			case 62: s = "\"extends\" expected"; break;
			case 63: s = "\"trait\" expected"; break;
			case 64: s = "\"ghost\" expected"; break;
			case 65: s = "\"static\" expected"; break;
			case 66: s = "\"datatype\" expected"; break;
			case 67: s = "\"codatatype\" expected"; break;
			case 68: s = "\"var\" expected"; break;
			case 69: s = "\"newtype\" expected"; break;
			case 70: s = "\"type\" expected"; break;
			case 71: s = "\"iterator\" expected"; break;
			case 72: s = "\"yields\" expected"; break;
			case 73: s = "\"returns\" expected"; break;
			case 74: s = "\"method\" expected"; break;
			case 75: s = "\"lemma\" expected"; break;
			case 76: s = "\"colemma\" expected"; break;
			case 77: s = "\"comethod\" expected"; break;
			case 78: s = "\"constructor\" expected"; break;
			case 79: s = "\"free\" expected"; break;
			case 80: s = "\"ensures\" expected"; break;
			case 81: s = "\"yield\" expected"; break;
			case 82: s = "\"function\" expected"; break;
			case 83: s = "\"predicate\" expected"; break;
			case 84: s = "\"copredicate\" expected"; break;
			case 85: s = "\"`\" expected"; break;
			case 86: s = "\"label\" expected"; break;
			case 87: s = "\"break\" expected"; break;
			case 88: s = "\"where\" expected"; break;
			case 89: s = "\":=\" expected"; break;
			case 90: s = "\"return\" expected"; break;
			case 91: s = "\":|\" expected"; break;
			case 92: s = "\"new\" expected"; break;
			case 93: s = "\"if\" expected"; break;
			case 94: s = "\"while\" expected"; break;
			case 95: s = "\"match\" expected"; break;
			case 96: s = "\"assert\" expected"; break;
			case 97: s = "\"print\" expected"; break;
			case 98: s = "\"forall\" expected"; break;
			case 99: s = "\"parallel\" expected"; break;
			case 100: s = "\"modify\" expected"; break;
			case 101: s = "\"#\" expected"; break;
			case 102: s = "\"<=\" expected"; break;
			case 103: s = "\">=\" expected"; break;
			case 104: s = "\"\\u2264\" expected"; break;
			case 105: s = "\"\\u2265\" expected"; break;
			case 106: s = "\"<==>\" expected"; break;
			case 107: s = "\"\\u21d4\" expected"; break;
			case 108: s = "\"==>\" expected"; break;
			case 109: s = "\"\\u21d2\" expected"; break;
			case 110: s = "\"<==\" expected"; break;
			case 111: s = "\"\\u21d0\" expected"; break;
			case 112: s = "\"&&\" expected"; break;
			case 113: s = "\"\\u2227\" expected"; break;
			case 114: s = "\"||\" expected"; break;
			case 115: s = "\"\\u2228\" expected"; break;
			case 116: s = "\"!\" expected"; break;
			case 117: s = "\"\\u00ac\" expected"; break;
			case 118: s = "\"\\u2200\" expected"; break;
			case 119: s = "\"exists\" expected"; break;
			case 120: s = "\"\\u2203\" expected"; break;
			case 121: s = "\"in\" expected"; break;
			case 122: s = "\"+\" expected"; break;
			case 123: s = "\"-\" expected"; break;
			case 124: s = "\"/\" expected"; break;
			case 125: s = "\"%\" expected"; break;
			case 126: s = "\"false\" expected"; break;
			case 127: s = "\"true\" expected"; break;
			case 128: s = "\"null\" expected"; break;
			case 129: s = "\"this\" expected"; break;
			case 130: s = "\"fresh\" expected"; break;
			case 131: s = "\"old\" expected"; break;
			case 132: s = "\"..\" expected"; break;
			case 133: s = "??? expected"; break;
			case 134: s = "this symbol not expected in SubModuleDecl"; break;
			case 135: s = "invalid SubModuleDecl"; break;
			case 136: s = "this symbol not expected in ClassDecl"; break;
			case 137: s = "this symbol not expected in DatatypeDecl"; break;
			case 138: s = "invalid DatatypeDecl"; break;
			case 139: s = "this symbol not expected in DatatypeDecl"; break;
			case 140: s = "invalid NewtypeDecl"; break;
			case 141: s = "invalid OtherTypeDecl"; break;
			case 142: s = "this symbol not expected in OtherTypeDecl"; break;
			case 143: s = "this symbol not expected in IteratorDecl"; break;
			case 144: s = "invalid IteratorDecl"; break;
			case 145: s = "this symbol not expected in TraitDecl"; break;
			case 146: s = "invalid ClassMemberDecl"; break;
			case 147: s = "this symbol not expected in FieldDecl"; break;
			case 148: s = "invalid FunctionDecl"; break;
			case 149: s = "invalid FunctionDecl"; break;
			case 150: s = "invalid FunctionDecl"; break;
			case 151: s = "invalid FunctionDecl"; break;
			case 152: s = "this symbol not expected in MethodDecl"; break;
			case 153: s = "invalid MethodDecl"; break;
			case 154: s = "invalid MethodDecl"; break;
			case 155: s = "invalid FIdentType"; break;
			case 156: s = "this symbol not expected in OldSemi"; break;
			case 157: s = "invalid TypeIdentOptional"; break;
			case 158: s = "invalid TypeAndToken"; break;
			case 159: s = "this symbol not expected in IteratorSpec"; break;
			case 160: s = "invalid IteratorSpec"; break;
			case 161: s = "invalid IteratorSpec"; break;
			case 162: s = "this symbol not expected in MethodSpec"; break;
			case 163: s = "invalid MethodSpec"; break;
			case 164: s = "invalid MethodSpec"; break;
			case 165: s = "invalid FrameExpression"; break;
			case 166: s = "invalid ReferenceType"; break;
			case 167: s = "this symbol not expected in FunctionSpec"; break;
			case 168: s = "invalid FunctionSpec"; break;
			case 169: s = "invalid PossiblyWildFrameExpression"; break;
			case 170: s = "invalid PossiblyWildExpression"; break;
			case 171: s = "this symbol not expected in OneStmt"; break;
			case 172: s = "invalid OneStmt"; break;
			case 173: s = "this symbol not expected in OneStmt"; break;
			case 174: s = "invalid OneStmt"; break;
			case 175: s = "invalid AssertStmt"; break;
			case 176: s = "invalid AssumeStmt"; break;
			case 177: s = "invalid UpdateStmt"; break;
			case 178: s = "invalid UpdateStmt"; break;
			case 179: s = "this symbol not expected in VarDeclStatement"; break;
			case 180: s = "invalid IfStmt"; break;
			case 181: s = "invalid IfStmt"; break;
			case 182: s = "invalid WhileStmt"; break;
			case 183: s = "invalid WhileStmt"; break;
			case 184: s = "invalid MatchStmt"; break;
			case 185: s = "invalid ForallStmt"; break;
			case 186: s = "invalid ForallStmt"; break;
			case 187: s = "invalid CalcStmt"; break;
			case 188: s = "invalid ModifyStmt"; break;
			case 189: s = "this symbol not expected in ModifyStmt"; break;
			case 190: s = "invalid ModifyStmt"; break;
			case 191: s = "invalid ReturnStmt"; break;
			case 192: s = "invalid Rhs"; break;
			case 193: s = "invalid Lhs"; break;
			case 194: s = "invalid Guard"; break;
			case 195: s = "this symbol not expected in LoopSpec"; break;
			case 196: s = "this symbol not expected in LoopSpec"; break;
			case 197: s = "this symbol not expected in LoopSpec"; break;
			case 198: s = "invalid LoopSpec"; break;
			case 199: s = "this symbol not expected in CaseStatement"; break;
			case 200: s = "this symbol not expected in CaseStatement"; break;
			case 201: s = "invalid CalcOp"; break;
			case 202: s = "invalid EquivOp"; break;
			case 203: s = "invalid ImpliesOp"; break;
			case 204: s = "invalid ExpliesOp"; break;
			case 205: s = "invalid AndOp"; break;
			case 206: s = "invalid OrOp"; break;
			case 207: s = "invalid NegOp"; break;
			case 208: s = "invalid Forall"; break;
			case 209: s = "invalid Exists"; break;
			case 210: s = "invalid QSep"; break;
			case 211: s = "invalid ImpliesExpliesExpression"; break;
			case 212: s = "invalid LogicalExpression"; break;
			case 213: s = "invalid RelOp"; break;
			case 214: s = "invalid AddOp"; break;
			case 215: s = "invalid UnaryExpression"; break;
			case 216: s = "invalid MulOp"; break;
			case 217: s = "invalid Suffix"; break;
			case 218: s = "invalid Suffix"; break;
			case 219: s = "invalid Suffix"; break;
			case 220: s = "invalid Suffix"; break;
			case 221: s = "invalid LambdaExpression"; break;
			case 222: s = "invalid EndlessExpression"; break;
			case 223: s = "invalid NameSegment"; break;
			case 224: s = "invalid DisplayExpr"; break;
			case 225: s = "invalid MultiSetExpr"; break;
			case 226: s = "invalid ConstAtomExpression"; break;
			case 227: s = "invalid Nat"; break;
			case 228: s = "invalid LambdaArrow"; break;
			case 229: s = "invalid MatchExpression"; break;
			case 230: s = "invalid QuantifierGuts"; break;
			case 231: s = "invalid StmtInExpr"; break;
			case 232: s = "invalid LetExpr"; break;
			case 233: s = "invalid CasePattern"; break;
			case 234: s = "invalid DotSuffix"; break;

			default: s = "error " + n; break;
		}
		return s;
	}

	public void SemErr(IToken/*!*/ tok, string/*!*/ msg) {  // semantic errors
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		SemErr(tok.filename, tok.line, tok.col, msg);
	}

	public virtual void SemErr(string filename, int line, int col, string/*!*/ msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(errMsgFormat, filename, line, col, msg);
		count++;
	}

	public void Warning(IToken/*!*/ tok, string/*!*/ msg) {  // warnings
		Contract.Requires(tok != null);
		Contract.Requires(msg != null);
		Warning(tok.filename, tok.line, tok.col, msg);
	}

	public virtual void Warning(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(warningMsgFormat, filename, line, col, msg);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}


}