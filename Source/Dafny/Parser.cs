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
	public const int _charToken = 6;
	public const int _stringToken = 7;
	public const int _colon = 8;
	public const int _verticalbar = 9;
	public const int _semi = 10;
	public const int _darrow = 11;
	public const int _arrow = 12;
	public const int _reads = 13;
	public const int _requires = 14;
	public const int _lbrace = 15;
	public const int _rbrace = 16;
	public const int _openparen = 17;
	public const int _closeparen = 18;
	public const int _star = 19;
	public const int _notIn = 20;
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
  return la.kind == _lbrace && x.val == "case";
}

bool IsLoopSpec() {
  return la.val == "invariant" | la.val == "decreases" | la.val == "modifies";
}

bool IsLoopSpecOrAlternative() {
  Token x = scanner.Peek();
  return IsLoopSpec() || (la.kind == _lbrace && x.val == "case");
}

bool IsParenStar() {
  scanner.ResetPeek();
  Token x = scanner.Peek();
  return la.kind == _openparen && x.kind == _star;
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
  return allowLambda &&
    (la.kind == _darrow || la.kind == _arrow
    || la.kind == _reads || la.kind == _requires);
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
  return allowSemi && la.kind == _semi &&
    (e is FunctionCallExpr || e is ApplyExpr ||
     (e is IdentifierSequence && ((IdentifierSequence)e).OpenParen != null));
}

bool CloseOptionalParen(bool usesOptionalParen) {
  return usesOptionalParen && la.kind == _closeparen;
}

bool CloseOptionalBrace(bool usesOptionalBrace) {
  return usesOptionalBrace && la.kind == _rbrace;
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
		
		while (la.kind == 21) {
			Get();
			Expect(7);
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
			case 22: case 23: case 25: {
				SubModuleDecl(defaultModule, out submodule);
				defaultModule.TopLevelDecls.Add(submodule); 
				break;
			}
			case 30: {
				ClassDecl(defaultModule, out c);
				defaultModule.TopLevelDecls.Add(c); 
				break;
			}
			case 35: case 36: {
				DatatypeDecl(defaultModule, out dt);
				defaultModule.TopLevelDecls.Add(dt); 
				break;
			}
			case 39: {
				NewtypeDecl(defaultModule, out td);
				defaultModule.TopLevelDecls.Add(td); 
				break;
			}
			case 40: {
				OtherTypeDecl(defaultModule, out td);
				defaultModule.TopLevelDecls.Add(td); 
				break;
			}
			case 42: {
				IteratorDecl(defaultModule, out iter);
				defaultModule.TopLevelDecls.Add(iter); 
				break;
			}
			case 32: {
				TraitDecl(defaultModule, out trait);
				defaultModule.TopLevelDecls.Add(trait); 
				break;
			}
			case 33: case 34: case 37: case 48: case 49: case 50: case 51: case 52: case 70: case 71: case 72: {
				ClassMemberDecl(membersDefaultClass, false);
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
		
		if (la.kind == 22 || la.kind == 23) {
			if (la.kind == 22) {
				Get();
				isAbstract = true; 
			}
			Expect(23);
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 24) {
				Get();
				QualifiedName(out idRefined);
			}
			module = new ModuleDefinition(id, id.val, isAbstract, false, idRefined == null ? null : idRefined, parent, attrs, false); 
			Expect(15);
			module.BodyStartTok = t; 
			while (StartOf(1)) {
				switch (la.kind) {
				case 22: case 23: case 25: {
					SubModuleDecl(module, out sm);
					module.TopLevelDecls.Add(sm); 
					break;
				}
				case 30: {
					ClassDecl(module, out c);
					module.TopLevelDecls.Add(c); 
					break;
				}
				case 32: {
					TraitDecl(module, out trait);
					module.TopLevelDecls.Add(trait); 
					break;
				}
				case 35: case 36: {
					DatatypeDecl(module, out dt);
					module.TopLevelDecls.Add(dt); 
					break;
				}
				case 39: {
					NewtypeDecl(module, out td);
					module.TopLevelDecls.Add(td); 
					break;
				}
				case 40: {
					OtherTypeDecl(module, out td);
					module.TopLevelDecls.Add(td); 
					break;
				}
				case 42: {
					IteratorDecl(module, out iter);
					module.TopLevelDecls.Add(iter); 
					break;
				}
				case 33: case 34: case 37: case 48: case 49: case 50: case 51: case 52: case 70: case 71: case 72: {
					ClassMemberDecl(namedModuleDefaultClassMembers, false);
					break;
				}
				}
			}
			Expect(16);
			module.BodyEndTok = t;
			module.TopLevelDecls.Add(new DefaultClassDecl(module, namedModuleDefaultClassMembers));
			submodule = new LiteralModuleDecl(module, parent); 
		} else if (la.kind == 25) {
			Get();
			if (la.kind == 26) {
				Get();
				opened = true;
			}
			NoUSIdent(out id);
			if (la.kind == 27 || la.kind == 28) {
				if (la.kind == 27) {
					Get();
					QualifiedName(out idPath);
					submodule = new AliasModuleDecl(idPath, id, parent, opened); 
				} else {
					Get();
					QualifiedName(out idPath);
					if (la.kind == 29) {
						Get();
						QualifiedName(out idAssignment);
					}
					submodule = new ModuleFacadeDecl(idPath, id, parent, idAssignment, opened); 
				}
			}
			if (la.kind == 10) {
				while (!(la.kind == 0 || la.kind == 10)) {SynErr(134); Get();}
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
		List<IToken>/*!*/ traitId=null;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		
		while (!(la.kind == 0 || la.kind == 30)) {SynErr(136); Get();}
		Expect(30);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 46) {
			GenericParameters(typeArgs);
		}
		if (la.kind == 31) {
			Get();
			QualifiedName(out traitId);
		}
		Expect(15);
		bodyStart = t; 
		while (StartOf(2)) {
			ClassMemberDecl(members, true);
		}
		Expect(16);
		c = new ClassDecl(id, id.val, module, typeArgs, members, attrs, traitId);
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
		
		while (!(la.kind == 0 || la.kind == 35 || la.kind == 36)) {SynErr(137); Get();}
		if (la.kind == 35) {
			Get();
		} else if (la.kind == 36) {
			Get();
			co = true; 
		} else SynErr(138);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 46) {
			GenericParameters(typeArgs);
		}
		Expect(27);
		bodyStart = t; 
		DatatypeMemberDecl(ctors);
		while (la.kind == 9) {
			Get();
			DatatypeMemberDecl(ctors);
		}
		if (la.kind == 10) {
			while (!(la.kind == 0 || la.kind == 10)) {SynErr(139); Get();}
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
		
		Expect(39);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		Expect(27);
		if (IsIdentColonOrBar()) {
			NoUSIdent(out bvId);
			if (la.kind == 8) {
				Get();
				Type(out baseType);
			}
			if (baseType == null) { baseType = new OperationTypeProxy(true, true, false, false, false); } 
			Expect(9);
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
		
		Expect(40);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 17) {
			Get();
			Expect(41);
			Expect(18);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
			if (la.kind == 46) {
				GenericParameters(typeArgs);
			}
		} else if (StartOf(4)) {
			if (la.kind == 46) {
				GenericParameters(typeArgs);
			}
			if (la.kind == 27) {
				Get();
				Type(out ty);
				td = new TypeSynonymDecl(id, id.val, typeArgs, module, ty, attrs); 
			}
		} else SynErr(141);
		if (td == null) {
		 td = new OpaqueTypeDecl(id, id.val, module, eqSupport, typeArgs, attrs);
		}
		
		if (la.kind == 10) {
			while (!(la.kind == 0 || la.kind == 10)) {SynErr(142); Get();}
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
		
		while (!(la.kind == 0 || la.kind == 42)) {SynErr(143); Get();}
		Expect(42);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 17 || la.kind == 46) {
			if (la.kind == 46) {
				GenericParameters(typeArgs);
			}
			Formals(true, true, ins);
			if (la.kind == 43 || la.kind == 44) {
				if (la.kind == 43) {
					Get();
				} else {
					Get();
					SemErr(t, "iterators don't have a 'returns' clause; did you mean 'yields'?"); 
				}
				Formals(false, true, outs);
			}
		} else if (la.kind == 45) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(144);
		while (StartOf(5)) {
			IteratorSpec(reads, mod, decreases, req, ens, yieldReq, yieldEns, ref readsAttrs, ref modAttrs, ref decrAttrs);
		}
		if (la.kind == 15) {
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
		
		while (!(la.kind == 0 || la.kind == 32)) {SynErr(145); Get();}
		Expect(32);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 46) {
			GenericParameters(typeArgs);
		}
		Expect(15);
		bodyStart = t; 
		while (StartOf(2)) {
			ClassMemberDecl(members, true);
		}
		Expect(16);
		trait = new TraitDecl(id, id.val, module, typeArgs, members, attrs);
		trait.BodyStartTok = bodyStart;
		trait.BodyEndTok = t;
		
	}

	void ClassMemberDecl(List<MemberDecl/*!*/>/*!*/ mm, bool allowConstructors) {
		Contract.Requires(cce.NonNullElements(mm));
		Method/*!*/ m;
		Function/*!*/ f;
		MemberModifiers mmod = new MemberModifiers();
		
		while (la.kind == 33 || la.kind == 34) {
			if (la.kind == 33) {
				Get();
				mmod.IsGhost = true; 
			} else {
				Get();
				mmod.IsStatic = true; 
			}
		}
		if (la.kind == 37) {
			FieldDecl(mmod, mm);
		} else if (la.kind == 70 || la.kind == 71 || la.kind == 72) {
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (StartOf(6)) {
			MethodDecl(mmod, allowConstructors, out m);
			mm.Add(m); 
		} else SynErr(146);
	}

	void Attribute(ref Attributes attrs) {
		Expect(15);
		AttributeBody(ref attrs);
		Expect(16);
	}

	void NoUSIdent(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t;
		if (x.val.StartsWith("_")) {
		 SemErr("cannot declare identifier beginning with underscore");
		}
		
	}

	void QualifiedName(out List<IToken> ids) {
		IToken id; IToken idPrime; ids = new List<IToken>(); 
		Ident(out id);
		ids.Add(id); 
		while (la.kind == 69) {
			IdentOrDigitsSuffix(out id, out idPrime);
			ids.Add(id);
			if (idPrime != null) { ids.Add(idPrime); }
			
		}
	}

	void Ident(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t; 
	}

	void IdentOrDigitsSuffix(out IToken x, out IToken y) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		x = Token.NoToken;
		y = null;
		
		Expect(69);
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
			 SemErr(x, "invalid IdentOrDigitsSuffix");
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
			
		} else if (la.kind == 14) {
			Get();
			x = t; 
		} else if (la.kind == 13) {
			Get();
			x = t; 
		} else SynErr(147);
	}

	void GenericParameters(List<TypeParameter/*!*/>/*!*/ typeArgs) {
		Contract.Requires(cce.NonNullElements(typeArgs));
		IToken/*!*/ id;
		TypeParameter.EqualitySupportValue eqSupport;
		
		Expect(46);
		NoUSIdent(out id);
		eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
		if (la.kind == 17) {
			Get();
			Expect(41);
			Expect(18);
			eqSupport = TypeParameter.EqualitySupportValue.Required; 
		}
		typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		while (la.kind == 38) {
			Get();
			NoUSIdent(out id);
			eqSupport = TypeParameter.EqualitySupportValue.Unspecified; 
			if (la.kind == 17) {
				Get();
				Expect(41);
				Expect(18);
				eqSupport = TypeParameter.EqualitySupportValue.Required; 
			}
			typeArgs.Add(new TypeParameter(id, id.val, eqSupport)); 
		}
		Expect(47);
	}

	void FieldDecl(MemberModifiers mmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		IToken/*!*/ id;  Type/*!*/ ty;
		
		while (!(la.kind == 0 || la.kind == 37)) {SynErr(148); Get();}
		Expect(37);
		if (mmod.IsStatic) { SemErr(t, "fields cannot be declared 'static'"); }
		
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		FIdentType(out id, out ty);
		mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		while (la.kind == 38) {
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
		
		if (la.kind == 70) {
			Get();
			if (la.kind == 48) {
				Get();
				isFunctionMethod = true; 
			}
			if (mmod.IsGhost) { SemErr(t, "functions cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (la.kind == 17 || la.kind == 46) {
				if (la.kind == 46) {
					GenericParameters(typeArgs);
				}
				Formals(true, isFunctionMethod, formals);
				Expect(8);
				Type(out returnType);
			} else if (la.kind == 45) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(149);
		} else if (la.kind == 71) {
			Get();
			isPredicate = true; 
			if (la.kind == 48) {
				Get();
				isFunctionMethod = true; 
			}
			if (mmod.IsGhost) { SemErr(t, "predicates cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (StartOf(7)) {
				if (la.kind == 46) {
					GenericParameters(typeArgs);
				}
				missingOpenParen = true; 
				if (la.kind == 17) {
					Formals(true, isFunctionMethod, formals);
					missingOpenParen = false; 
				}
				if (missingOpenParen) { errors.Warning(t, "with the new support of higher-order functions in Dafny, parentheses-less predicates are no longer supported; in the new syntax, parentheses are required for the declaration and uses of predicates, even if the predicate takes no additional arguments"); } 
				if (la.kind == 8) {
					Get();
					SemErr(t, "predicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 45) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(150);
		} else if (la.kind == 72) {
			Get();
			isCoPredicate = true; 
			if (mmod.IsGhost) { SemErr(t, "copredicates cannot be declared 'ghost' (they are ghost by default)"); }
			
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			NoUSIdent(out id);
			if (StartOf(7)) {
				if (la.kind == 46) {
					GenericParameters(typeArgs);
				}
				missingOpenParen = true; 
				if (la.kind == 17) {
					Formals(true, isFunctionMethod, formals);
					missingOpenParen = false; 
				}
				if (missingOpenParen) { errors.Warning(t, "with the new support of higher-order functions in Dafny, parentheses-less co-predicates are no longer supported; in the new syntax, parentheses are required for the declaration and uses of predicates, even if the co-predicate takes no additional arguments"); } 
				if (la.kind == 8) {
					Get();
					SemErr(t, "copredicates do not have an explicitly declared return type; it is always bool"); 
				}
			} else if (la.kind == 45) {
				Get();
				signatureEllipsis = t; 
			} else SynErr(151);
		} else SynErr(152);
		decreases = isCoPredicate ? null : new List<Expression/*!*/>(); 
		while (StartOf(8)) {
			FunctionSpec(reqs, reads, ens, decreases);
		}
		if (la.kind == 15) {
			FunctionBody(out body, out bodyStart, out bodyEnd);
		}
		if (DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 && !Attributes.Contains(attrs, "axiom")) {
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
		 theBuiltIns.CreateArrowTypeDecl(formals.Count);
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
		
		while (!(StartOf(9))) {SynErr(153); Get();}
		if (la.kind == 48) {
			Get();
		} else if (la.kind == 49) {
			Get();
			isLemma = true; 
		} else if (la.kind == 50) {
			Get();
			isCoLemma = true; 
		} else if (la.kind == 51) {
			Get();
			isCoLemma = true;
			errors.Warning(t, "the 'comethod' keyword has been deprecated; it has been renamed to 'colemma'");
			
		} else if (la.kind == 52) {
			Get();
			if (allowConstructor) {
			 isConstructor = true;
			} else {
			 SemErr(t, "constructors are allowed only in classes");
			}
			
		} else SynErr(154);
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
		
		while (la.kind == 15) {
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
		
		if (la.kind == 17 || la.kind == 46) {
			if (la.kind == 46) {
				GenericParameters(typeArgs);
			}
			Formals(true, !mmod.IsGhost, ins);
			if (la.kind == 44) {
				Get();
				if (isConstructor) { SemErr(t, "constructors cannot have out-parameters"); } 
				Formals(false, !mmod.IsGhost, outs);
			}
		} else if (la.kind == 45) {
			Get();
			signatureEllipsis = t; 
		} else SynErr(155);
		while (StartOf(10)) {
			MethodSpec(req, mod, ens, dec, ref decAttrs, ref modAttrs);
		}
		if (la.kind == 15) {
			BlockStmt(out body, out bodyStart, out bodyEnd);
		}
		if (Attributes.Contains(attrs, "axiom") && !mmod.IsGhost && !isLemma) {
		  SemErr(t, "only ghost methods can have the :axiom attribute");
		}
		
		if (DafnyOptions.O.DisallowSoundnessCheating && body == null && ens.Count > 0 && !Attributes.Contains(attrs, "axiom")) {
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
		
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		NoUSIdent(out id);
		if (la.kind == 17) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(17);
		if (StartOf(11)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 38) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(18);
	}

	void FIdentType(out IToken/*!*/ id, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		id = Token.NoToken;
		
		if (la.kind == 1) {
			WildIdent(out id, false);
		} else if (la.kind == 2) {
			Get();
			id = t; 
		} else SynErr(156);
		Expect(8);
		Type(out ty);
	}

	void OldSemi() {
		if (la.kind == 10) {
			while (!(la.kind == 0 || la.kind == 10)) {SynErr(157); Get();}
			Get();
		}
	}

	void Type(out Type ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; 
		TypeAndToken(out tok, out ty);
	}

	void Expression(out Expression e, bool allowSemi, bool allowLambda) {
		Expression e0; IToken endTok; 
		EquivExpression(out e, allowSemi, allowLambda);
		if (SemiFollowsCall(allowSemi, e)) {
			Expect(10);
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
		if (la.kind == 33) {
			Get();
			if (allowGhostKeyword) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
		}
		IdentType(out id, out ty, true);
	}

	void IdentType(out IToken/*!*/ id, out Type/*!*/ ty, bool allowWildcardId) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		WildIdent(out id, allowWildcardId);
		Expect(8);
		Type(out ty);
	}

	void WildIdent(out IToken/*!*/ x, bool allowWildcardId) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t;
		t.val = UnwildIdent(x.val, allowWildcardId);
		
	}

	void LocalIdentTypeOptional(out LocalVariable var, bool isGhost) {
		IToken id;  Type ty;  Type optType = null;
		
		WildIdent(out id, true);
		if (la.kind == 8) {
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
		if (la.kind == 8) {
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
		if (la.kind == 33) {
			Get();
			isGhost = true; 
		}
		if (StartOf(3)) {
			TypeAndToken(out id, out ty);
			if (la.kind == 8) {
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
			Expect(8);
			Type(out ty);
		} else SynErr(158);
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
		case 58: {
			Get();
			tok = t; 
			break;
		}
		case 59: {
			Get();
			tok = t;  ty = new CharType(); 
			break;
		}
		case 60: {
			Get();
			tok = t;  ty = new NatType(); 
			break;
		}
		case 61: {
			Get();
			tok = t;  ty = new IntType(); 
			break;
		}
		case 62: {
			Get();
			tok = t;  ty = new RealType(); 
			break;
		}
		case 63: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 46) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("set type expects only one type argument");
			}
			ty = new SetType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 64: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 46) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("multiset type expects only one type argument");
			}
			ty = new MultiSetType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 65: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 46) {
				GenericInstantiation(gt);
			}
			if (gt.Count > 1) {
			 SemErr("seq type expects only one type argument");
			}
			ty = new SeqType(gt.Count == 1 ? gt[0] : null);
			
			break;
		}
		case 66: {
			Get();
			tok = t;  ty = new UserDefinedType(tok, tok.val, new List<Type>(), new List<IToken>()); 
			break;
		}
		case 67: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			if (la.kind == 46) {
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
		case 17: {
			Get();
			tok = t; gt = new List<Type>(); 
			if (StartOf(3)) {
				Type(out ty);
				gt.Add(ty); 
				while (la.kind == 38) {
					Get();
					Type(out ty);
					gt.Add(ty); 
				}
			}
			Expect(18);
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
		case 1: case 5: case 68: {
			ReferenceType(out tok, out ty);
			break;
		}
		default: SynErr(159); break;
		}
		if (la.kind == 12) {
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
		Expect(17);
		if (la.kind == 1 || la.kind == 33) {
			GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 38) {
				Get();
				GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(18);
	}

	void IteratorSpec(List<FrameExpression/*!*/>/*!*/ reads, List<FrameExpression/*!*/>/*!*/ mod, List<Expression/*!*/> decreases,
List<MaybeFreeExpression/*!*/>/*!*/ req, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<MaybeFreeExpression/*!*/>/*!*/ yieldReq, List<MaybeFreeExpression/*!*/>/*!*/ yieldEns,
ref Attributes readsAttrs, ref Attributes modAttrs, ref Attributes decrAttrs) {
		Expression/*!*/ e; FrameExpression/*!*/ fe; bool isFree = false; bool isYield = false; Attributes ensAttrs = null;
		
		while (!(StartOf(12))) {SynErr(160); Get();}
		if (la.kind == 13) {
			Get();
			while (IsAttribute()) {
				Attribute(ref readsAttrs);
			}
			if (StartOf(13)) {
				FrameExpression(out fe);
				reads.Add(fe); 
				while (la.kind == 38) {
					Get();
					FrameExpression(out fe);
					reads.Add(fe); 
				}
			}
			OldSemi();
		} else if (la.kind == 53) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			if (StartOf(13)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 38) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			}
			OldSemi();
		} else if (StartOf(14)) {
			if (la.kind == 54) {
				Get();
				isFree = true; 
			}
			if (la.kind == 57) {
				Get();
				isYield = true; 
			}
			if (la.kind == 14) {
				Get();
				Expression(out e, false, true);
				OldSemi();
				if (isYield) {
				 yieldReq.Add(new MaybeFreeExpression(e, isFree));
				} else {
				 req.Add(new MaybeFreeExpression(e, isFree));
				}
				
			} else if (la.kind == 55) {
				Get();
				while (IsAttribute()) {
					Attribute(ref ensAttrs);
				}
				Expression(out e, false, true);
				OldSemi();
				if (isYield) {
				 yieldEns.Add(new MaybeFreeExpression(e, isFree, ensAttrs));
				} else {
				 ens.Add(new MaybeFreeExpression(e, isFree, ensAttrs));
				}
				
			} else SynErr(161);
		} else if (la.kind == 56) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decrAttrs);
			}
			DecreasesList(decreases, false);
			OldSemi();
		} else SynErr(162);
	}

	void BlockStmt(out BlockStmt/*!*/ block, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out block) != null);
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(15);
		bodyStart = t; 
		while (StartOf(15)) {
			Stmt(body);
		}
		Expect(16);
		bodyEnd = t;
		block = new BlockStmt(bodyStart, bodyEnd, body); 
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases, ref Attributes decAttrs, ref Attributes modAttrs) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false; Attributes ensAttrs = null;
		
		while (!(StartOf(16))) {SynErr(163); Get();}
		if (la.kind == 53) {
			Get();
			while (IsAttribute()) {
				Attribute(ref modAttrs);
			}
			if (StartOf(13)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 38) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			}
			OldSemi();
		} else if (la.kind == 14 || la.kind == 54 || la.kind == 55) {
			if (la.kind == 54) {
				Get();
				isFree = true; 
			}
			if (la.kind == 14) {
				Get();
				Expression(out e, false, true);
				OldSemi();
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 55) {
				Get();
				while (IsAttribute()) {
					Attribute(ref ensAttrs);
				}
				Expression(out e, false, true);
				OldSemi();
				ens.Add(new MaybeFreeExpression(e, isFree, ensAttrs)); 
			} else SynErr(164);
		} else if (la.kind == 56) {
			Get();
			while (IsAttribute()) {
				Attribute(ref decAttrs);
			}
			DecreasesList(decreases, true);
			OldSemi();
		} else SynErr(165);
	}

	void FrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null);
		Expression/*!*/ e;
		IToken/*!*/ id;
		string fieldName = null;  IToken feTok = null;
		fe = null;
		
		if (StartOf(17)) {
			Expression(out e, false, false);
			feTok = e.tok; 
			if (la.kind == 73) {
				Get();
				Ident(out id);
				fieldName = id.val;  feTok = id; 
			}
			fe = new FrameExpression(feTok, e, fieldName); 
		} else if (la.kind == 73) {
			Get();
			Ident(out id);
			fieldName = id.val; 
			fe = new FrameExpression(id, new ImplicitThisExpr(id), fieldName); 
		} else SynErr(166);
	}

	void DecreasesList(List<Expression/*!*/> decreases, bool allowWildcard) {
		Expression/*!*/ e; 
		PossiblyWildExpression(out e);
		if (!allowWildcard && e is WildcardExpr) {
		 SemErr(e.tok, "'decreases *' is allowed only on loops and tail-recursive methods");
		} else {
		 decreases.Add(e);
		}
		
		while (la.kind == 38) {
			Get();
			PossiblyWildExpression(out e);
			if (!allowWildcard && e is WildcardExpr) {
			 SemErr(e.tok, "'decreases *' is allowed only on loops and tail-recursive methods");
			} else {
			 decreases.Add(e);
			}
			
		}
	}

	void GenericInstantiation(List<Type/*!*/>/*!*/ gt) {
		Contract.Requires(cce.NonNullElements(gt)); Type/*!*/ ty; 
		Expect(46);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 38) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(47);
	}

	void ReferenceType(out IToken/*!*/ tok, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type> gt;
		List<IToken> path;
		
		if (la.kind == 68) {
			Get();
			tok = t;  ty = new ObjectType(); 
		} else if (la.kind == 5) {
			Get();
			tok = t;  gt = new List<Type>(); 
			if (la.kind == 46) {
				GenericInstantiation(gt);
			}
			int dims = tok.val.Length == 5 ? 1 : int.Parse(tok.val.Substring(5));
			ty = theBuiltIns.ArrayType(tok, dims, gt, true);
			
		} else if (la.kind == 1) {
			Ident(out tok);
			gt = new List<Type>();
			path = new List<IToken>(); 
			while (la.kind == 69) {
				path.Add(tok); 
				Get();
				Ident(out tok);
			}
			if (la.kind == 46) {
				GenericInstantiation(gt);
			}
			ty = new UserDefinedType(tok, tok.val, gt, path); 
		} else SynErr(167);
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/> decreases) {
		Contract.Requires(cce.NonNullElements(reqs));
		Contract.Requires(cce.NonNullElements(reads));
		Contract.Requires(decreases == null || cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		if (la.kind == 14) {
			while (!(la.kind == 0 || la.kind == 14)) {SynErr(168); Get();}
			Get();
			Expression(out e, false, true);
			OldSemi();
			reqs.Add(e); 
		} else if (la.kind == 13) {
			Get();
			if (StartOf(18)) {
				PossiblyWildFrameExpression(out fe);
				reads.Add(fe); 
				while (la.kind == 38) {
					Get();
					PossiblyWildFrameExpression(out fe);
					reads.Add(fe); 
				}
			}
			OldSemi();
		} else if (la.kind == 55) {
			Get();
			Expression(out e, false, true);
			OldSemi();
			ens.Add(e); 
		} else if (la.kind == 56) {
			Get();
			if (decreases == null) {
			 SemErr(t, "'decreases' clauses are meaningless for copredicates, so they are not allowed");
			 decreases = new List<Expression/*!*/>();
			}
			
			DecreasesList(decreases, false);
			OldSemi();
		} else SynErr(169);
	}

	void FunctionBody(out Expression/*!*/ e, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); e = dummyExpr; 
		Expect(15);
		bodyStart = t; 
		Expression(out e, true, true);
		Expect(16);
		bodyEnd = t; 
	}

	void PossiblyWildFrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); fe = dummyFrameExpr; 
		if (la.kind == 19) {
			Get();
			fe = new FrameExpression(t, new WildcardExpr(t), null); 
		} else if (StartOf(13)) {
			FrameExpression(out fe);
		} else SynErr(170);
	}

	void LambdaSpec(out Expression req, List<FrameExpression> reads) {
		Contract.Requires(reads != null);
		Expression e; req = null;  FrameExpression fe; 
		while (la.kind == 13 || la.kind == 14) {
			if (la.kind == 14) {
				Get();
				Expression(out e, false, false);
				if (req == null) {
				 req = e;
				} else {
				 req = new BinaryExpr(req.tok, BinaryExpr.Opcode.And, req, e);
				}
				
			} else {
				Get();
				PossiblyWildFrameExpression(out fe);
				reads.Add(fe); 
			}
		}
	}

	void PossiblyWildExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 19) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(17)) {
			Expression(out e, false, false);
		} else SynErr(171);
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
		
		while (!(StartOf(19))) {SynErr(172); Get();}
		switch (la.kind) {
		case 15: {
			BlockStmt(out bs, out bodyStart, out bodyEnd);
			s = bs; 
			break;
		}
		case 90: {
			AssertStmt(out s);
			break;
		}
		case 80: {
			AssumeStmt(out s);
			break;
		}
		case 91: {
			PrintStmt(out s);
			break;
		}
		case 1: case 2: case 3: case 4: case 6: case 7: case 9: case 17: case 61: case 62: case 120: case 121: case 122: case 123: case 124: case 125: {
			UpdateStmt(out s);
			break;
		}
		case 33: case 37: {
			VarDeclStatement(out s);
			break;
		}
		case 84: {
			IfStmt(out s);
			break;
		}
		case 87: {
			WhileStmt(out s);
			break;
		}
		case 89: {
			MatchStmt(out s);
			break;
		}
		case 92: case 93: {
			ForallStmt(out s);
			break;
		}
		case 95: {
			CalcStmt(out s);
			break;
		}
		case 94: {
			ModifyStmt(out s);
			break;
		}
		case 74: {
			Get();
			x = t; 
			NoUSIdent(out id);
			Expect(8);
			OneStmt(out s);
			s.Labels = new LList<Label>(new Label(x, id.val), s.Labels); 
			break;
		}
		case 75: {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				NoUSIdent(out id);
				label = id.val; 
			} else if (la.kind == 10 || la.kind == 75) {
				while (la.kind == 75) {
					Get();
					breakCount++; 
				}
			} else SynErr(173);
			while (!(la.kind == 0 || la.kind == 10)) {SynErr(174); Get();}
			Expect(10);
			s = label != null ? new BreakStmt(x, t, label) : new BreakStmt(x, t, breakCount); 
			break;
		}
		case 57: case 78: {
			ReturnStmt(out s);
			break;
		}
		case 45: {
			SkeletonStmt(out s);
			break;
		}
		default: SynErr(175); break;
		}
	}

	void AssertStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;
		Expression e = dummyExpr; Attributes attrs = null;
		IToken dotdotdot = null;
		
		Expect(90);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(17)) {
			Expression(out e, false, true);
		} else if (la.kind == 45) {
			Get();
			dotdotdot = t; 
		} else SynErr(176);
		Expect(10);
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
		
		Expect(80);
		x = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(17)) {
			Expression(out e, false, true);
		} else if (la.kind == 45) {
			Get();
			dotdotdot = t; 
		} else SynErr(177);
		Expect(10);
		if (dotdotdot != null) {
		 s = new SkeletonStatement(new AssumeStmt(x, t, new LiteralExpr(x, true), attrs), dotdotdot, null);
		} else {
		 s = new AssumeStmt(x, t, e, attrs);
		}
		
	}

	void PrintStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression arg;
		List<Expression> args = new List<Expression>();
		
		Expect(91);
		x = t; 
		AttributeArg(out arg, false);
		args.Add(arg); 
		while (la.kind == 38) {
			Get();
			AttributeArg(out arg, false);
			args.Add(arg); 
		}
		Expect(10);
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
		if (la.kind == 10 || la.kind == 15) {
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			Expect(10);
			endTok = t; rhss.Add(new ExprRhs(e, attrs)); 
		} else if (la.kind == 38 || la.kind == 77 || la.kind == 79) {
			lhss.Add(e);  lhs0 = e; 
			while (la.kind == 38) {
				Get();
				Lhs(out e);
				lhss.Add(e); 
			}
			if (la.kind == 77) {
				Get();
				x = t; 
				Rhs(out r, lhs0);
				rhss.Add(r); 
				while (la.kind == 38) {
					Get();
					Rhs(out r, lhs0);
					rhss.Add(r); 
				}
			} else if (la.kind == 79) {
				Get();
				x = t; 
				if (la.kind == 80) {
					Get();
					suchThatAssume = t; 
				}
				Expression(out suchThat, false, true);
			} else SynErr(178);
			Expect(10);
			endTok = t; 
		} else if (la.kind == 8) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(179);
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
		
		if (la.kind == 33) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(37);
		if (!isGhost) { x = t; } 
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		LocalIdentTypeOptional(out d, isGhost);
		lhss.Add(d); d.Attributes = attrs; attrs = null; 
		while (la.kind == 38) {
			Get();
			while (la.kind == 15) {
				Attribute(ref attrs);
			}
			LocalIdentTypeOptional(out d, isGhost);
			lhss.Add(d); d.Attributes = attrs; attrs = null; 
		}
		if (la.kind == 77 || la.kind == 79) {
			if (la.kind == 77) {
				Get();
				assignTok = t;
				lhs0 = new IdentifierExpr(lhss[0].Tok, lhss[0].Name);
				
				Rhs(out r, lhs0);
				rhss.Add(r); 
				while (la.kind == 38) {
					Get();
					Rhs(out r, lhs0);
					rhss.Add(r); 
				}
			} else {
				Get();
				assignTok = t; 
				if (la.kind == 80) {
					Get();
					suchThatAssume = t; 
				}
				Expression(out suchThat, false, true);
			}
		}
		Expect(10);
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
		
		Expect(84);
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
			if (la.kind == 85) {
				Get();
				if (la.kind == 84) {
					IfStmt(out s);
					els = s; endTok = s.EndTok; 
				} else if (la.kind == 15) {
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

	void WhileStmt(out Statement/*!*/ stmt) {
		Contract.Ensures(Contract.ValueAtReturn(out stmt) != null); IToken/*!*/ x;
		Expression guard = null;  IToken guardEllipsis = null;
		List<MaybeFreeExpression/*!*/> invariants = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> decreases = new List<Expression/*!*/>();
		Attributes decAttrs = null;
		Attributes modAttrs = null;
		List<FrameExpression/*!*/> mod = null;
		BlockStmt/*!*/ body = null;  IToken bodyEllipsis = null;
		IToken bodyStart = null, bodyEnd = null, endTok = Token.NoToken;
		List<GuardedAlternative> alternatives;
		stmt = dummyStmt;  // to please the compiler
		
		Expect(87);
		x = t; 
		if (IsLoopSpecOrAlternative()) {
			LoopSpec(out invariants, out decreases, out mod, ref decAttrs, ref modAttrs);
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
			LoopSpec(out invariants, out decreases, out mod, ref decAttrs, ref modAttrs);
			if (la.kind == 15) {
				BlockStmt(out body, out bodyStart, out bodyEnd);
				endTok = body.EndTok; 
			} else if (la.kind == 45) {
				Get();
				bodyEllipsis = t; endTok = t; 
			} else SynErr(182);
			if (guardEllipsis != null || bodyEllipsis != null) {
			 if (mod != null) {
			   SemErr(mod[0].E.tok, "'modifies' clauses are not allowed on refining loops");
			 }
			 if (body == null) {
			   body = new BlockStmt(x, endTok, new List<Statement>());
			 }
			 stmt = new WhileStmt(x, endTok, guard, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(null, null), body);
			 stmt = new SkeletonStatement(stmt, guardEllipsis, bodyEllipsis);
			} else {
			 // The following statement protects against crashes in case of parsing errors
			 body = body ?? new BlockStmt(x, endTok, new List<Statement>());
			 stmt = new WhileStmt(x, endTok, guard, invariants, new Specification<Expression>(decreases, decAttrs), new Specification<FrameExpression>(mod, modAttrs), body);
			}
			
		} else SynErr(183);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(89);
		x = t; 
		Expression(out e, true, true);
		if (la.kind == 15) {
			Get();
			usesOptionalBrace = true; 
		}
		while (la.kind == 86) {
			CaseStatement(out c);
			cases.Add(c); 
		}
		if (CloseOptionalBrace(usesOptionalBrace)) {
			Expect(16);
		} else if (StartOf(22)) {
			if (usesOptionalBrace) { SemErr(t, "expecting close curly brace"); } 
		} else SynErr(184);
		s = new MatchStmt(x, t, e, cases, usesOptionalBrace); 
	}

	void ForallStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		IToken/*!*/ x = Token.NoToken;
		bool usesOptionalParen = false;
		List<BoundVar/*!*/> bvars = null;
		Attributes attrs = null;
		Expression range = null;
		var ens = new List<MaybeFreeExpression/*!*/>();
		bool isFree;
		Expression/*!*/ e;
		BlockStmt block = null;
		IToken bodyStart, bodyEnd;
		IToken tok = Token.NoToken;
		
		if (la.kind == 92) {
			Get();
			x = t; tok = x; 
		} else if (la.kind == 93) {
			Get();
			x = t;
			errors.Warning(t, "the 'parallel' keyword has been deprecated; the comprehension statement now uses the keyword 'forall' (and the parentheses around the bound variables are now optional)");
			
		} else SynErr(185);
		if (la.kind == 17) {
			Get();
			usesOptionalParen = true; 
		}
		if (la.kind == 1) {
			List<BoundVar/*!*/> bvarsX;  Attributes attrsX;  Expression rangeX; 
			QuantifierDomain(out bvarsX, out attrsX, out rangeX);
			bvars = bvarsX; attrs = attrsX; range = rangeX;
			
		}
		if (bvars == null) { bvars = new List<BoundVar>(); }
		if (range == null) { range = new LiteralExpr(x, true); }
		
		if (CloseOptionalParen(usesOptionalParen)) {
			Expect(18);
		} else if (StartOf(23)) {
			if (usesOptionalParen) { SemErr(t, "expecting close parenthesis"); } 
		} else SynErr(186);
		while (la.kind == 54 || la.kind == 55) {
			isFree = false; 
			if (la.kind == 54) {
				Get();
				isFree = true; 
			}
			Expect(55);
			Expression(out e, false, true);
			ens.Add(new MaybeFreeExpression(e, isFree)); 
			OldSemi();
			tok = t; 
		}
		if (la.kind == 15) {
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

	void CalcStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;
		CalcStmt.CalcOp/*!*/ op, calcOp = Microsoft.Dafny.CalcStmt.DefaultOp, resOp = Microsoft.Dafny.CalcStmt.DefaultOp;
		var lines = new List<Expression/*!*/>();
		var hints = new List<BlockStmt/*!*/>();
		CalcStmt.CalcOp stepOp;
		var stepOps = new List<CalcStmt.CalcOp>();
		CalcStmt.CalcOp maybeOp;
		Expression/*!*/ e;
		BlockStmt/*!*/ h;
		IToken opTok;
		IToken danglingOperator = null;
		
		Expect(95);
		x = t; 
		if (StartOf(24)) {
			CalcOp(out opTok, out calcOp);
			maybeOp = calcOp.ResultOp(calcOp); // guard against non-transitive calcOp (like !=)
			if (maybeOp == null) {
			 SemErr(opTok, "the main operator of a calculation must be transitive");
			}
			resOp = calcOp;
			
		}
		Expect(15);
		while (StartOf(17)) {
			Expression(out e, false, true);
			lines.Add(e); stepOp = calcOp; danglingOperator = null; 
			Expect(10);
			if (StartOf(24)) {
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
			Hint(out h);
			hints.Add(h);
			if (h.Body.Count != 0) { danglingOperator = null; }
			
		}
		Expect(16);
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
		
		Expect(94);
		tok = t; 
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (StartOf(25)) {
			if (StartOf(13)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 38) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			} else {
				Get();
				ellipsisToken = t; 
			}
		}
		if (la.kind == 15) {
			BlockStmt(out body, out bodyStart, out endTok);
		} else if (la.kind == 10) {
			while (!(la.kind == 0 || la.kind == 10)) {SynErr(187); Get();}
			Get();
			endTok = t; 
		} else SynErr(188);
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
		
		if (la.kind == 78) {
			Get();
			returnTok = t; 
		} else if (la.kind == 57) {
			Get();
			returnTok = t; isYield = true; 
		} else SynErr(189);
		if (StartOf(26)) {
			Rhs(out r, null);
			rhss = new List<AssignmentRhs>(); rhss.Add(r); 
			while (la.kind == 38) {
				Get();
				Rhs(out r, null);
				rhss.Add(r); 
			}
		}
		Expect(10);
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
		Expect(45);
		dotdotdot = t; 
		if (la.kind == 76) {
			Get();
			names = new List<IToken>(); exprs = new List<Expression>(); whereTok = t;
			Ident(out tok);
			names.Add(tok); 
			while (la.kind == 38) {
				Get();
				Ident(out tok);
				names.Add(tok); 
			}
			Expect(77);
			Expression(out e, false, true);
			exprs.Add(e); 
			while (la.kind == 38) {
				Get();
				Expression(out e, false, true);
				exprs.Add(e); 
			}
			if (exprs.Count != names.Count) {
			 SemErr(whereTok, exprs.Count < names.Count ? "not enough expressions" : "too many expressions");
			 names = null; exprs = null;
			}
			
		}
		Expect(10);
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
		
		if (la.kind == 81) {
			Get();
			newToken = t; 
			TypeAndToken(out x, out ty);
			if (la.kind == 17 || la.kind == 69 || la.kind == 82) {
				if (la.kind == 82) {
					Get();
					ee = new List<Expression>(); 
					Expressions(ee);
					Expect(83);
					var tmp = theBuiltIns.ArrayType(ee.Count, new IntType(), true);
					
				} else {
					x = null; args = new List<Expression/*!*/>(); 
					if (la.kind == 69) {
						Get();
						Ident(out x);
					}
					Expect(17);
					if (StartOf(17)) {
						Expressions(args);
					}
					Expect(18);
				}
			}
			if (ee != null) {
			 r = new TypeRhs(newToken, ty, ee);
			} else if (args != null) {
			 r = new TypeRhs(newToken, ty, x == null ? null : x.val, receiverForInitCall, args);
			} else {
			 r = new TypeRhs(newToken, ty);
			}
			
		} else if (la.kind == 19) {
			Get();
			r = new HavocRhs(t); 
		} else if (StartOf(17)) {
			Expression(out e, false, true);
			r = new ExprRhs(e); 
		} else SynErr(190);
		while (la.kind == 15) {
			Attribute(ref attrs);
		}
		r.Attributes = attrs; 
	}

	void Lhs(out Expression e) {
		e = dummyExpr;  // the assignment is to please the compiler, the dummy value to satisfy contracts in the event of a parse error
		
		if (la.kind == 1) {
			DottedIdentifiersAndFunction(out e, false, false);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
			ApplySuffix(ref e);
		} else if (StartOf(27)) {
			ConstAtomExpression(out e, false, false);
			Suffix(ref e);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
		} else SynErr(191);
	}

	void Expressions(List<Expression/*!*/>/*!*/ args) {
		Contract.Requires(cce.NonNullElements(args)); Expression/*!*/ e; 
		Expression(out e, true, true);
		args.Add(e); 
		while (la.kind == 38) {
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
		
		Expect(15);
		while (la.kind == 86) {
			Get();
			x = t; 
			Expression(out e, true, false);
			Expect(11);
			body = new List<Statement>(); 
			while (StartOf(15)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, e, body)); 
		}
		Expect(16);
		endTok = t; 
	}

	void Guard(out Expression e) {
		Expression/*!*/ ee;  e = null; 
		if (la.kind == 19) {
			Get();
			e = null; 
		} else if (IsParenStar()) {
			Expect(17);
			Expect(19);
			Expect(18);
			e = null; 
		} else if (StartOf(17)) {
			Expression(out ee, true, true);
			e = ee; 
		} else SynErr(192);
	}

	void LoopSpec(out List<MaybeFreeExpression/*!*/> invariants, out List<Expression/*!*/> decreases, out List<FrameExpression/*!*/> mod, ref Attributes decAttrs, ref Attributes modAttrs) {
		FrameExpression/*!*/ fe;
		invariants = new List<MaybeFreeExpression/*!*/>();
		MaybeFreeExpression invariant = null;
		decreases = new List<Expression/*!*/>();
		mod = null;
		
		while (StartOf(28)) {
			if (la.kind == 54 || la.kind == 88) {
				Invariant(out invariant);
				OldSemi();
				invariants.Add(invariant); 
			} else if (la.kind == 56) {
				while (!(la.kind == 0 || la.kind == 56)) {SynErr(193); Get();}
				Get();
				while (IsAttribute()) {
					Attribute(ref decAttrs);
				}
				DecreasesList(decreases, true);
				OldSemi();
			} else {
				while (!(la.kind == 0 || la.kind == 53)) {SynErr(194); Get();}
				Get();
				while (IsAttribute()) {
					Attribute(ref modAttrs);
				}
				mod = mod ?? new List<FrameExpression>(); 
				if (StartOf(13)) {
					FrameExpression(out fe);
					mod.Add(fe); 
					while (la.kind == 38) {
						Get();
						FrameExpression(out fe);
						mod.Add(fe); 
					}
				}
				OldSemi();
			}
		}
	}

	void Invariant(out MaybeFreeExpression/*!*/ invariant) {
		bool isFree = false; Expression/*!*/ e; List<string> ids = new List<string>(); invariant = null; Attributes attrs = null; 
		while (!(la.kind == 0 || la.kind == 54 || la.kind == 88)) {SynErr(195); Get();}
		if (la.kind == 54) {
			Get();
			isFree = true; 
		}
		Expect(88);
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		Expression(out e, false, true);
		invariant = new MaybeFreeExpression(e, isFree, attrs); 
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(86);
		x = t; 
		Ident(out id);
		if (la.kind == 17) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 38) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(18);
		}
		Expect(11);
		while (StartOf(15)) {
			Stmt(body);
		}
		c = new MatchCaseStmt(x, id.val, arguments, body); 
	}

	void AttributeArg(out Expression arg, bool allowSemi) {
		Contract.Ensures(Contract.ValueAtReturn(out arg) != null); Expression/*!*/ e;  arg = dummyExpr; 
		Expression(out e, allowSemi, true);
		arg = e; 
	}

	void QuantifierDomain(out List<BoundVar> bvars, out Attributes attrs, out Expression range) {
		bvars = new List<BoundVar>();
		BoundVar/*!*/ bv;
		attrs = null;
		range = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 38) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (IsAttribute()) {
			Attribute(ref attrs);
		}
		if (la.kind == 9) {
			Get();
			Expression(out range, true, true);
		}
	}

	void CalcOp(out IToken x, out CalcStmt.CalcOp/*!*/ op) {
		var binOp = BinaryExpr.Opcode.Eq; // Returns Eq if parsing fails because it is compatible with any other operator
		Expression k = null;
		x = null;
		
		switch (la.kind) {
		case 41: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Eq; 
			if (la.kind == 96) {
				Get();
				Expect(82);
				Expression(out k, true, true);
				Expect(83);
			}
			break;
		}
		case 46: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 47: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 97: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 98: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 99: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 100: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 101: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Le; 
			break;
		}
		case 102: {
			Get();
			x = t;  binOp = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 103: case 104: {
			EquivOp();
			x = t;  binOp = BinaryExpr.Opcode.Iff; 
			break;
		}
		case 105: case 106: {
			ImpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Imp; 
			break;
		}
		case 107: case 108: {
			ExpliesOp();
			x = t;  binOp = BinaryExpr.Opcode.Exp; 
			break;
		}
		default: SynErr(196); break;
		}
		if (k == null) {
		 op = new Microsoft.Dafny.CalcStmt.BinaryCalcOp(binOp);
		} else {
		 op = new Microsoft.Dafny.CalcStmt.TernaryCalcOp(k);
		}
		
	}

	void Hint(out BlockStmt s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); // returns an empty block statement if the hint is empty
		var subhints = new List<Statement/*!*/>();
		IToken bodyStart, bodyEnd;
		BlockStmt/*!*/ block;
		Statement/*!*/ calc;
		Token x = la;
		IToken endTok = x;
		
		while (la.kind == 15 || la.kind == 95) {
			if (la.kind == 15) {
				BlockStmt(out block, out bodyStart, out bodyEnd);
				endTok = block.EndTok; subhints.Add(block); 
			} else {
				CalcStmt(out calc);
				endTok = calc.EndTok; subhints.Add(calc); 
			}
		}
		s = new BlockStmt(x, endTok, subhints); // if the hint is empty x is the first token of the next line, but it doesn't matter cause the block statement is just used as a container
		
	}

	void EquivOp() {
		if (la.kind == 103) {
			Get();
		} else if (la.kind == 104) {
			Get();
		} else SynErr(197);
	}

	void ImpliesOp() {
		if (la.kind == 105) {
			Get();
		} else if (la.kind == 106) {
			Get();
		} else SynErr(198);
	}

	void ExpliesOp() {
		if (la.kind == 107) {
			Get();
		} else if (la.kind == 108) {
			Get();
		} else SynErr(199);
	}

	void EquivExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		ImpliesExpliesExpression(out e0, allowSemi, allowLambda);
		while (la.kind == 103 || la.kind == 104) {
			EquivOp();
			x = t; 
			ImpliesExpliesExpression(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Iff, e0, e1); 
		}
	}

	void ImpliesExpliesExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0, allowSemi, allowLambda);
		if (StartOf(29)) {
			if (la.kind == 105 || la.kind == 106) {
				ImpliesOp();
				x = t; 
				ImpliesExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
			} else {
				ExpliesOp();
				x = t; 
				LogicalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e0, e1); 
				while (la.kind == 107 || la.kind == 108) {
					ExpliesOp();
					x = t; 
					LogicalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Exp, e0, e1); 
				}
			}
		}
	}

	void LogicalExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0, allowSemi, allowLambda);
		if (StartOf(30)) {
			if (la.kind == 109 || la.kind == 110) {
				AndOp();
				x = t; 
				RelationalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				while (la.kind == 109 || la.kind == 110) {
					AndOp();
					x = t; 
					RelationalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				}
			} else {
				OrOp();
				x = t; 
				RelationalExpression(out e1, allowSemi, allowLambda);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				while (la.kind == 111 || la.kind == 112) {
					OrOp();
					x = t; 
					RelationalExpression(out e1, allowSemi, allowLambda);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesExpression(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0, allowSemi, allowLambda);
		if (la.kind == 105 || la.kind == 106) {
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
		if (StartOf(31)) {
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
			
			while (StartOf(31)) {
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

	void AndOp() {
		if (la.kind == 109) {
			Get();
		} else if (la.kind == 110) {
			Get();
		} else SynErr(200);
	}

	void OrOp() {
		if (la.kind == 111) {
			Get();
		} else if (la.kind == 112) {
			Get();
		} else SynErr(201);
	}

	void Term(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		Factor(out e0, allowSemi, allowLambda);
		while (la.kind == 115 || la.kind == 116) {
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
		case 41: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			if (la.kind == 96) {
				Get();
				Expect(82);
				Expression(out k, true, true);
				Expect(83);
			}
			break;
		}
		case 46: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 47: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 97: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 98: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 99: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			if (la.kind == 96) {
				Get();
				Expect(82);
				Expression(out k, true, true);
				Expect(83);
			}
			break;
		}
		case 113: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 20: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 114: {
			Get();
			x = t;  y = Token.NoToken; 
			if (la.kind == 114) {
				Get();
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
		case 100: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 101: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 102: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(202); break;
		}
	}

	void Factor(out Expression e0, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0, allowSemi, allowLambda);
		while (la.kind == 19 || la.kind == 117 || la.kind == 118) {
			MulOp(out x, out op);
			UnaryExpression(out e1, allowSemi, allowLambda);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 115) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 116) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(203);
	}

	void UnaryExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		switch (la.kind) {
		case 116: {
			Get();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new NegationExpression(x, e); 
			break;
		}
		case 114: case 119: {
			NegOp();
			x = t; 
			UnaryExpression(out e, allowSemi, allowLambda);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Not, e); 
			break;
		}
		case 33: case 37: case 63: case 74: case 80: case 84: case 89: case 90: case 92: case 95: case 128: case 129: case 130: {
			EndlessExpression(out e, allowSemi, allowLambda);
			break;
		}
		case 1: {
			DottedIdentifiersAndFunction(out e, allowSemi, allowLambda);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
			ApplySuffix(ref e);
			break;
		}
		case 15: case 82: {
			DisplayExpr(out e);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
			break;
		}
		case 64: {
			MultiSetExpr(out e);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
			break;
		}
		case 67: {
			Get();
			x = t; 
			if (la.kind == 82) {
				MapDisplayExpr(x, out e);
				while (la.kind == 69 || la.kind == 82) {
					Suffix(ref e);
				}
			} else if (la.kind == 1) {
				MapComprehensionExpr(x, out e, allowSemi);
			} else if (StartOf(32)) {
				SemErr("map must be followed by literal in brackets or comprehension."); 
			} else SynErr(204);
			break;
		}
		case 2: case 3: case 4: case 6: case 7: case 9: case 17: case 61: case 62: case 120: case 121: case 122: case 123: case 124: case 125: {
			ConstAtomExpression(out e, allowSemi, allowLambda);
			while (la.kind == 69 || la.kind == 82) {
				Suffix(ref e);
			}
			break;
		}
		default: SynErr(205); break;
		}
	}

	void MulOp(out IToken x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 19) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 117) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 118) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(206);
	}

	void NegOp() {
		if (la.kind == 114) {
			Get();
		} else if (la.kind == 119) {
			Get();
		} else SynErr(207);
	}

	void EndlessExpression(out Expression e, bool allowSemi, bool allowLambda) {
		IToken/*!*/ x;
		Expression e0, e1;
		Statement s;
		e = dummyExpr;
		
		switch (la.kind) {
		case 84: {
			Get();
			x = t; 
			Expression(out e, true, true);
			Expect(126);
			Expression(out e0, true, true);
			Expect(85);
			Expression(out e1, allowSemi, allowLambda);
			e = new ITEExpr(x, e, e0, e1); 
			break;
		}
		case 89: {
			MatchExpression(out e, allowSemi, allowLambda);
			break;
		}
		case 92: case 128: case 129: case 130: {
			QuantifierGuts(out e, allowSemi, allowLambda);
			break;
		}
		case 63: {
			ComprehensionExpr(out e, allowSemi, allowLambda);
			break;
		}
		case 80: case 90: case 95: {
			StmtInExpr(out s);
			Expression(out e, allowSemi, allowLambda);
			e = new StmtExpr(s.Tok, s, e); 
			break;
		}
		case 33: case 37: {
			LetExpr(out e, allowSemi, allowLambda);
			break;
		}
		case 74: {
			NamedExpr(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(208); break;
		}
	}

	void DottedIdentifiersAndFunction(out Expression e, bool allowSemi, bool allowLambda) {
		IToken id, idPrime;  IToken openParen = null;
		List<Expression> args = null;
		List<IToken> idents = new List<IToken>();
		e = null;
		var applyArgLists = new List<List<Expression>>();
		
		Ident(out id);
		idents.Add(id); 
		while (la.kind == 69) {
			IdentOrDigitsSuffix(out id, out idPrime);
			idents.Add(id);
			if (idPrime != null) { idents.Add(idPrime); id = idPrime; }
			
		}
		if (la.kind == 17 || la.kind == 96) {
			args = new List<Expression>(); 
			if (la.kind == 96) {
				Get();
				id.val = id.val + "#";  Expression k; 
				Expect(82);
				Expression(out k, true, true);
				Expect(83);
				args.Add(k); 
			}
			Expect(17);
			openParen = t; 
			if (StartOf(17)) {
				Expressions(args);
			}
			Expect(18);
		}
		if (IsLambda(allowLambda)) {
			Expression body = null;
			Expression req = null;
			bool oneShot;
			var reads = new List<FrameExpression>();
			
			LambdaSpec(out req, reads);
			LambdaArrow(out oneShot);
			Expression(out body, allowSemi, true);
			if (idents.Count != 1) {
			 SemErr(id, "Invalid variable binding in lambda.");
			}
			if (args != null) {
			 SemErr(openParen, "Expected variable binding.");
			}
			BoundVar bv = new BoundVar(id, UnwildIdent(id.val, true),  new InferredTypeProxy());
			e = new LambdaExpr(id, oneShot, new List<BoundVar>{ bv }, req, reads, body);
			theBuiltIns.CreateArrowTypeDecl(1);
			
		}
		if (e == null) {
		 e = new IdentifierSequence(idents, openParen, args);
		 foreach (var args_ in applyArgLists) {
		   e = new ApplyExpr(id, openParen, e, args_);
		 }
		}
		
	}

	void Suffix(ref Expression e) {
		Contract.Requires(e != null); Contract.Ensures(e!=null); IToken/*!*/ id, x;  List<Expression/*!*/>/*!*/ args;
		Expression e0 = null;  Expression e1 = null;  Expression/*!*/ ee;  bool anyDots = false; List<Expression> multipleLengths = null; bool takeRest = false;
		List<Expression> multipleIndices = null;
		bool func = false;
		
		if (la.kind == 69) {
			IdentOrDigitsSuffix(out id, out x);
			if (x != null) {
			 // process id as a Suffix in its own right
			 e = new ExprDotName(id, e, id.val);
			 id = x;  // move to the next Suffix
			}
			
			if (la.kind == 17 || la.kind == 96) {
				args = new List<Expression/*!*/>();  func = true; 
				if (la.kind == 96) {
					Get();
					id.val = id.val + "#";  Expression k; 
					Expect(82);
					Expression(out k, true, true);
					Expect(83);
					args.Add(k); 
				}
				Expect(17);
				IToken openParen = t; 
				if (StartOf(17)) {
					Expressions(args);
				}
				Expect(18);
				e = new FunctionCallExpr(id, id.val, e, openParen, args); 
			}
			if (!func) { e = new ExprDotName(id, e, id.val); } 
		} else if (la.kind == 82) {
			Get();
			x = t; 
			if (StartOf(17)) {
				Expression(out ee, true, true);
				e0 = ee; 
				if (la.kind == 127) {
					Get();
					anyDots = true; 
					if (StartOf(17)) {
						Expression(out ee, true, true);
						e1 = ee; 
					}
				} else if (la.kind == 77) {
					Get();
					Expression(out ee, true, true);
					e1 = ee; 
				} else if (la.kind == 8 || la.kind == 83) {
					while (la.kind == 8) {
						Get();
						if (multipleLengths == null) {
						 multipleLengths = new List<Expression>();
						 multipleLengths.Add(e0);
						}
						takeRest = true;
						
						if (StartOf(17)) {
							Expression(out ee, true, true);
							multipleLengths.Add(ee);
							takeRest = false;
							
						}
					}
				} else if (la.kind == 38 || la.kind == 83) {
					while (la.kind == 38) {
						Get();
						Expression(out ee, true, true);
						if (multipleIndices == null) {
						multipleIndices = new List<Expression>();
						multipleIndices.Add(e0);
						}
						multipleIndices.Add(ee);
						
					}
				} else SynErr(209);
			} else if (la.kind == 127) {
				Get();
				anyDots = true; 
				if (StartOf(17)) {
					Expression(out ee, true, true);
					e1 = ee; 
				}
			} else SynErr(210);
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
			 } else if (multipleLengths != null || takeRest) {
			   Expression prev = new LiteralExpr(x, 0);
			   List<Expression> seqs = new List<Expression>();
			   if (multipleLengths != null)
			   {
			     foreach (var len in multipleLengths)
			     {
			       var end = new BinaryExpr(x, BinaryExpr.Opcode.Add, prev, len);
			       seqs.Add(new SeqSelectExpr(x, false, e, prev, end));
			       prev = end;
			     }
			   }
			   if (takeRest)
			   {
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
			
			Expect(83);
		} else SynErr(211);
		ApplySuffix(ref e);
	}

	void ApplySuffix(ref Expression e) {
		while (la.kind == 17) {
			Get();
			IToken openParen = t; var args = new List<Expression>(); 
			if (StartOf(17)) {
				Expressions(args);
			}
			Expect(18);
			e = new ApplyExpr(e.tok, openParen, e, args); 
		}
	}

	void DisplayExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		if (la.kind == 15) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(17)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements);
			Expect(16);
		} else if (la.kind == 82) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(17)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(83);
		} else SynErr(212);
	}

	void MultiSetExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		Expect(64);
		x = t; 
		if (la.kind == 15) {
			Get();
			elements = new List<Expression/*!*/>(); 
			if (StartOf(17)) {
				Expressions(elements);
			}
			e = new MultiSetDisplayExpr(x, elements);
			Expect(16);
		} else if (la.kind == 17) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			Expression(out e, true, true);
			e = new MultiSetFormingExpr(x, e); 
			Expect(18);
		} else if (StartOf(32)) {
			SemErr("multiset must be followed by multiset literal or expression to coerce in parentheses."); 
		} else SynErr(213);
	}

	void MapDisplayExpr(IToken/*!*/ mapToken, out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		List<ExpressionPair/*!*/>/*!*/ elements= new List<ExpressionPair/*!*/>() ;
		e = dummyExpr;
		
		Expect(82);
		if (StartOf(17)) {
			MapLiteralExpressions(out elements);
		}
		e = new MapDisplayExpr(mapToken, elements);
		Expect(83);
	}

	void MapComprehensionExpr(IToken mapToken, out Expression e, bool allowSemi) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		BoundVar bv;
		List<BoundVar> bvars = new List<BoundVar>();
		Expression range = null;
		Expression body;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		if (la.kind == 9) {
			Get();
			Expression(out range, true, true);
		}
		QSep();
		Expression(out body, allowSemi, true);
		e = new MapComprehension(mapToken, bvars, range ?? new LiteralExpr(mapToken, true), body);
		
	}

	void ConstAtomExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;   Basetypes.BigDec d;
		e = dummyExpr;  Type toType = null;
		
		switch (la.kind) {
		case 120: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 121: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 122: {
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
		case 6: {
			Get();
			e = new CharLiteralExpr(t, t.val.Substring(1, t.val.Length - 2)); 
			break;
		}
		case 7: {
			Get();
			bool isVerbatimString;
			string s = Util.RemoveParsedStringQuotes(t.val, out isVerbatimString);
			e = new StringLiteralExpr(t, s, isVerbatimString);
			
			break;
		}
		case 123: {
			Get();
			e = new ThisExpr(t); 
			break;
		}
		case 124: {
			Get();
			x = t; 
			Expect(17);
			Expression(out e, true, true);
			Expect(18);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Fresh, e); 
			break;
		}
		case 125: {
			Get();
			x = t; 
			Expect(17);
			Expression(out e, true, true);
			Expect(18);
			e = new OldExpr(x, e); 
			break;
		}
		case 9: {
			Get();
			x = t; 
			Expression(out e, true, true);
			e = new UnaryOpExpr(x, UnaryOpExpr.Opcode.Cardinality, e); 
			Expect(9);
			break;
		}
		case 61: case 62: {
			if (la.kind == 61) {
				Get();
				x = t; toType = new IntType(); 
			} else {
				Get();
				x = t; toType = new RealType(); 
			}
			Expect(17);
			Expression(out e, true, true);
			Expect(18);
			e = new ConversionExpr(x, e, toType); 
			break;
		}
		case 17: {
			ParensExpression(out e, allowSemi, allowLambda);
			break;
		}
		default: SynErr(214); break;
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
			
		} else SynErr(215);
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
		Expression ee;
		e = null;
		List<Expression> args = new List<Expression>();
		List<Type> types = new List<Type>();
		Type tt;
		bool isLambda = false;
		
		Expect(17);
		x = t; 
		if (StartOf(17)) {
			OptTypedExpr(out ee, out tt, true);
			args.Add(ee); types.Add(tt); 
			while (la.kind == 38) {
				Get();
				OptTypedExpr(out ee, out tt, true);
				args.Add(ee); types.Add(tt); 
			}
		}
		Expect(18);
		if (IsLambda(allowLambda)) {
			Expression body = null;
			Expression req = null;
			bool oneShot;
			var reads = new List<FrameExpression>();
			x = t;
			
			LambdaSpec(out req, reads);
			LambdaArrow(out oneShot);
			Expression(out body, allowSemi, true);
			List<BoundVar> bvs = new List<BoundVar>();
			for (int i = 0; i < args.Count; i++) {
			 ee = args[i];
			 tt = types[i];
			 if (ee is IdentifierSequence) {
			   IdentifierSequence ise = (IdentifierSequence)ee;
			   List<IToken> idents = ise.Tokens;
			   Contract.Assert(idents != null);
			   Contract.Assert(idents.Count > 0);
			   IToken id = idents[0];
			   if (idents.Count != 1) {
			     SemErr(id, "Expected variable binding.");
			   }
			   if (ise.Arguments != null) {
			     SemErr(ise.OpenParen, "Expected variable binding.");
			   }
			   bvs.Add(new BoundVar(id, UnwildIdent(id.val, true), tt ?? new InferredTypeProxy()));
			 } else {
			   SemErr(ee.tok, "Expected variable binding.");
			 }
			}
			e = new LambdaExpr(x, oneShot, bvs, req, reads, body);
			theBuiltIns.CreateArrowTypeDecl(bvs.Count);
			isLambda = true;
			
		}
		if (!isLambda) {
		 for (int i = 0; i < args.Count; i++) {
		   if (types[i] != null) {
		     SemErr(args[i].tok, "Type specification not allowed here, comma separator was expected.");
		   }
		 }
		 if (args.Count == 1) {
		   e = new ParensExpression(x, args[0]);
		 } else {
		   // make sure the corresponding tuple type exists
		   var tmp = theBuiltIns.TupleType(x, args.Count, true);
		   e = new DatatypeValue(x, BuiltIns.TupleTypeName(args.Count), BuiltIns.TupleTypeCtorName, args);
		 }
		}
		
		if (!isLambda && args.Count == 1 && la.kind == _openparen) {
			IToken openParen; 
			while (la.kind == 17) {
				Get();
				openParen = t; args = new List<Expression>(); 
				if (StartOf(17)) {
					Expressions(args);
				}
				Expect(18);
				e = new ApplyExpr(x, openParen, e, args); 
			}
		}
	}

	void LambdaArrow(out bool oneShot) {
		oneShot = true; 
		if (la.kind == 11) {
			Get();
			oneShot = false; 
		} else if (la.kind == 12) {
			Get();
			oneShot = true; 
		} else SynErr(216);
	}

	void OptTypedExpr(out Expression e, out Type tt, bool allowSemi) {
		tt = null; 
		Expression(out e, allowSemi, true);
		if (la.kind == 8) {
			Get();
			Type(out tt);
		}
	}

	void MapLiteralExpressions(out List<ExpressionPair> elements) {
		Expression/*!*/ d, r;
		elements = new List<ExpressionPair/*!*/>(); 
		Expression(out d, true, true);
		Expect(77);
		Expression(out r, true, true);
		elements.Add(new ExpressionPair(d,r)); 
		while (la.kind == 38) {
			Get();
			Expression(out d, true, true);
			Expect(77);
			Expression(out r, true, true);
			elements.Add(new ExpressionPair(d,r)); 
		}
	}

	void QSep() {
		if (la.kind == 131) {
			Get();
		} else if (la.kind == 132) {
			Get();
		} else SynErr(217);
	}

	void MatchExpression(out Expression e, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  MatchCaseExpr/*!*/ c;
		List<MatchCaseExpr/*!*/> cases = new List<MatchCaseExpr/*!*/>();
		bool usesOptionalBrace = false;
		
		Expect(89);
		x = t; 
		Expression(out e, allowSemi, true);
		if (la.kind == 15) {
			Get();
			usesOptionalBrace = true; 
		}
		while (la.kind == 86) {
			CaseExpression(out c, allowSemi, usesOptionalBrace || allowLambda);
			cases.Add(c); 
		}
		if (CloseOptionalBrace(usesOptionalBrace)) {
			Expect(16);
		} else if (StartOf(32)) {
			if (usesOptionalBrace) { SemErr(t, "expecting close curly brace"); } 
		} else SynErr(218);
		e = new MatchExpr(x, e, cases, usesOptionalBrace); 
	}

	void QuantifierGuts(out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		List<BoundVar/*!*/> bvars;
		Attributes attrs;
		Expression range;
		Expression/*!*/ body;
		
		if (la.kind == 92 || la.kind == 128) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 129 || la.kind == 130) {
			Exists();
			x = t; 
		} else SynErr(219);
		QuantifierDomain(out bvars, out attrs, out range);
		QSep();
		Expression(out body, allowSemi, allowLambda);
		if (univ) {
		 q = new ForallExpr(x, bvars, range, body, attrs);
		} else {
		 q = new ExistsExpr(x, bvars, range, body, attrs);
		}
		
	}

	void ComprehensionExpr(out Expression q, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null);
		IToken x = Token.NoToken;
		BoundVar bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar>();
		Expression range;
		Expression body = null;
		
		Expect(63);
		x = t; 
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 38) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		Expect(9);
		Expression(out range, allowSemi, allowLambda);
		if (la.kind == 131 || la.kind == 132) {
			QSep();
			Expression(out body, allowSemi, allowLambda);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(x, bvars, range, body);
		
	}

	void StmtInExpr(out Statement s) {
		s = dummyStmt; 
		if (la.kind == 90) {
			AssertStmt(out s);
		} else if (la.kind == 80) {
			AssumeStmt(out s);
		} else if (la.kind == 95) {
			CalcStmt(out s);
		} else SynErr(220);
	}

	void LetExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken x = null;
		bool isGhost = false;
		var letLHSs = new List<CasePattern>();
		var letRHSs = new List<Expression>();
		CasePattern pat;
		bool exact = true;
		e = dummyExpr;
		
		if (la.kind == 33) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(37);
		if (!isGhost) { x = t; } 
		CasePattern(out pat);
		if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
		letLHSs.Add(pat);
		
		while (la.kind == 38) {
			Get();
			CasePattern(out pat);
			if (isGhost) { pat.Vars.Iter(bv => bv.IsGhost = true); }
			letLHSs.Add(pat);
			
		}
		if (la.kind == 77) {
			Get();
		} else if (la.kind == 79) {
			Get();
			exact = false;
			foreach (var lhs in letLHSs) {
			 if (lhs.Arguments != null) {
			   SemErr(lhs.tok, "LHS of let-such-that expression must be variables, not general patterns");
			 }
			}
			
		} else SynErr(221);
		Expression(out e, false, true);
		letRHSs.Add(e); 
		while (la.kind == 38) {
			Get();
			Expression(out e, false, true);
			letRHSs.Add(e); 
		}
		Expect(10);
		Expression(out e, allowSemi, allowLambda);
		e = new LetExpr(x, letLHSs, letRHSs, e, exact); 
	}

	void NamedExpr(out Expression e, bool allowSemi, bool allowLambda) {
		IToken/*!*/ x, d;
		e = dummyExpr;
		Expression expr;
		
		Expect(74);
		x = t; 
		NoUSIdent(out d);
		Expect(8);
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
			Expect(17);
			arguments = new List<CasePattern>(); 
			if (la.kind == 1) {
				CasePattern(out pat);
				arguments.Add(pat); 
				while (la.kind == 38) {
					Get();
					CasePattern(out pat);
					arguments.Add(pat); 
				}
			}
			Expect(18);
			pat = new CasePattern(id, id.val, arguments); 
		} else if (la.kind == 1) {
			IdentTypeOptional(out bv);
			pat = new CasePattern(bv.tok, bv);
			
		} else SynErr(222);
		if (pat == null) {
		 pat = new CasePattern(t, "_ParseError", new List<CasePattern>());
		}
		
	}

	void CaseExpression(out MatchCaseExpr c, bool allowSemi, bool allowLambda) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		Expression/*!*/ body;
		
		Expect(86);
		x = t; 
		Ident(out id);
		if (la.kind == 17) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 38) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(18);
		}
		Expect(11);
		Expression(out body, allowSemi, allowLambda);
		c = new MatchCaseExpr(x, id.val, arguments, body); 
	}

	void Forall() {
		if (la.kind == 92) {
			Get();
		} else if (la.kind == 128) {
			Get();
		} else SynErr(223);
	}

	void Exists() {
		if (la.kind == 129) {
			Get();
		} else if (la.kind == 130) {
			Get();
		} else SynErr(224);
	}

	void AttributeBody(ref Attributes attrs) {
		string aName;
		List<Expression> aArgs = new List<Expression>();
		Expression aArg;
		
		Expect(8);
		Expect(1);
		aName = t.val; 
		if (StartOf(17)) {
			AttributeArg(out aArg, true);
			aArgs.Add(aArg); 
			while (la.kind == 38) {
				Get();
				AttributeArg(out aArg, true);
				aArgs.Add(aArg); 
			}
		}
		attrs = new Attributes(aName, aArgs, attrs); 
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
		{T,T,T,T, T,x,T,T, x,T,T,x, x,T,T,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,T,x,T, T,T,x,x, x,x,T,x, x,T,x,x, T,T,T,T, T,T,T,T, T,T,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,T,x, T,x,x,x, T,x,x,T, T,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, x,T,x,x, x,x,T,x, T,T,T,T, T,T,x,T, T,x,T,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, T,x,x,x, x,x,T,T, x,T,x,T, x,x,T,x, T,T,T,T, T,T,x,T, T,x,T,x, x,x,T,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, T,x,x,x, x,T,T,T, T,T,x,x, x,x,T,T, x,T,x,x, x,x,T,x, T,T,T,T, T,T,x,T, T,x,T,x, x,x,T,x, T,T,T,T, T,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,T,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,T,x, T,x,x,x, T,x,x,T, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,x,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,T,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{T,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,T,x, T,x,x,x, T,x,x,T, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,x,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,x,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,T,x, T,x,x,x, T,x,T,T, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,T,T, x,T,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,T,x, T,x,x,x, T,x,T,T, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,T,T,x, x,x,x,x, T,x,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,T,T,T, T,x,T,T, x,T,x,x, x,x,x,T, x,T,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,x,x,x, x,x,T,x, x,x,x,x, T,T,T,x, T,x,x,x, x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,T, T,T,T,T, T,T,x,x, T,T,T,x, x,x,x},
		{x,x,T,T, T,x,T,T, x,T,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,T,T,T, T,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,x,T,T, x,T,x,x, x,x,T,x, T,T,T,T, T,T,T,T, T,T,T,x, x,T,T,T, T,T,T,T, T,T,T,T, T,T,x,x, x,T,T,x, x,x,x,x, x,T,T,T, T,T,T,T, x,T,T,T, T,x,T,T, T,T,T,T, T,T,T,T, T,T,T,T, x,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,x, T,T,T,T, T,T,T,T, x,x,x,T, T,x,x}

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
			case 6: s = "charToken expected"; break;
			case 7: s = "stringToken expected"; break;
			case 8: s = "colon expected"; break;
			case 9: s = "verticalbar expected"; break;
			case 10: s = "semi expected"; break;
			case 11: s = "darrow expected"; break;
			case 12: s = "arrow expected"; break;
			case 13: s = "reads expected"; break;
			case 14: s = "requires expected"; break;
			case 15: s = "lbrace expected"; break;
			case 16: s = "rbrace expected"; break;
			case 17: s = "openparen expected"; break;
			case 18: s = "closeparen expected"; break;
			case 19: s = "star expected"; break;
			case 20: s = "notIn expected"; break;
			case 21: s = "\"include\" expected"; break;
			case 22: s = "\"abstract\" expected"; break;
			case 23: s = "\"module\" expected"; break;
			case 24: s = "\"refines\" expected"; break;
			case 25: s = "\"import\" expected"; break;
			case 26: s = "\"opened\" expected"; break;
			case 27: s = "\"=\" expected"; break;
			case 28: s = "\"as\" expected"; break;
			case 29: s = "\"default\" expected"; break;
			case 30: s = "\"class\" expected"; break;
			case 31: s = "\"extends\" expected"; break;
			case 32: s = "\"trait\" expected"; break;
			case 33: s = "\"ghost\" expected"; break;
			case 34: s = "\"static\" expected"; break;
			case 35: s = "\"datatype\" expected"; break;
			case 36: s = "\"codatatype\" expected"; break;
			case 37: s = "\"var\" expected"; break;
			case 38: s = "\",\" expected"; break;
			case 39: s = "\"newtype\" expected"; break;
			case 40: s = "\"type\" expected"; break;
			case 41: s = "\"==\" expected"; break;
			case 42: s = "\"iterator\" expected"; break;
			case 43: s = "\"yields\" expected"; break;
			case 44: s = "\"returns\" expected"; break;
			case 45: s = "\"...\" expected"; break;
			case 46: s = "\"<\" expected"; break;
			case 47: s = "\">\" expected"; break;
			case 48: s = "\"method\" expected"; break;
			case 49: s = "\"lemma\" expected"; break;
			case 50: s = "\"colemma\" expected"; break;
			case 51: s = "\"comethod\" expected"; break;
			case 52: s = "\"constructor\" expected"; break;
			case 53: s = "\"modifies\" expected"; break;
			case 54: s = "\"free\" expected"; break;
			case 55: s = "\"ensures\" expected"; break;
			case 56: s = "\"decreases\" expected"; break;
			case 57: s = "\"yield\" expected"; break;
			case 58: s = "\"bool\" expected"; break;
			case 59: s = "\"char\" expected"; break;
			case 60: s = "\"nat\" expected"; break;
			case 61: s = "\"int\" expected"; break;
			case 62: s = "\"real\" expected"; break;
			case 63: s = "\"set\" expected"; break;
			case 64: s = "\"multiset\" expected"; break;
			case 65: s = "\"seq\" expected"; break;
			case 66: s = "\"string\" expected"; break;
			case 67: s = "\"map\" expected"; break;
			case 68: s = "\"object\" expected"; break;
			case 69: s = "\".\" expected"; break;
			case 70: s = "\"function\" expected"; break;
			case 71: s = "\"predicate\" expected"; break;
			case 72: s = "\"copredicate\" expected"; break;
			case 73: s = "\"`\" expected"; break;
			case 74: s = "\"label\" expected"; break;
			case 75: s = "\"break\" expected"; break;
			case 76: s = "\"where\" expected"; break;
			case 77: s = "\":=\" expected"; break;
			case 78: s = "\"return\" expected"; break;
			case 79: s = "\":|\" expected"; break;
			case 80: s = "\"assume\" expected"; break;
			case 81: s = "\"new\" expected"; break;
			case 82: s = "\"[\" expected"; break;
			case 83: s = "\"]\" expected"; break;
			case 84: s = "\"if\" expected"; break;
			case 85: s = "\"else\" expected"; break;
			case 86: s = "\"case\" expected"; break;
			case 87: s = "\"while\" expected"; break;
			case 88: s = "\"invariant\" expected"; break;
			case 89: s = "\"match\" expected"; break;
			case 90: s = "\"assert\" expected"; break;
			case 91: s = "\"print\" expected"; break;
			case 92: s = "\"forall\" expected"; break;
			case 93: s = "\"parallel\" expected"; break;
			case 94: s = "\"modify\" expected"; break;
			case 95: s = "\"calc\" expected"; break;
			case 96: s = "\"#\" expected"; break;
			case 97: s = "\"<=\" expected"; break;
			case 98: s = "\">=\" expected"; break;
			case 99: s = "\"!=\" expected"; break;
			case 100: s = "\"\\u2260\" expected"; break;
			case 101: s = "\"\\u2264\" expected"; break;
			case 102: s = "\"\\u2265\" expected"; break;
			case 103: s = "\"<==>\" expected"; break;
			case 104: s = "\"\\u21d4\" expected"; break;
			case 105: s = "\"==>\" expected"; break;
			case 106: s = "\"\\u21d2\" expected"; break;
			case 107: s = "\"<==\" expected"; break;
			case 108: s = "\"\\u21d0\" expected"; break;
			case 109: s = "\"&&\" expected"; break;
			case 110: s = "\"\\u2227\" expected"; break;
			case 111: s = "\"||\" expected"; break;
			case 112: s = "\"\\u2228\" expected"; break;
			case 113: s = "\"in\" expected"; break;
			case 114: s = "\"!\" expected"; break;
			case 115: s = "\"+\" expected"; break;
			case 116: s = "\"-\" expected"; break;
			case 117: s = "\"/\" expected"; break;
			case 118: s = "\"%\" expected"; break;
			case 119: s = "\"\\u00ac\" expected"; break;
			case 120: s = "\"false\" expected"; break;
			case 121: s = "\"true\" expected"; break;
			case 122: s = "\"null\" expected"; break;
			case 123: s = "\"this\" expected"; break;
			case 124: s = "\"fresh\" expected"; break;
			case 125: s = "\"old\" expected"; break;
			case 126: s = "\"then\" expected"; break;
			case 127: s = "\"..\" expected"; break;
			case 128: s = "\"\\u2200\" expected"; break;
			case 129: s = "\"exists\" expected"; break;
			case 130: s = "\"\\u2203\" expected"; break;
			case 131: s = "\"::\" expected"; break;
			case 132: s = "\"\\u2022\" expected"; break;
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
			case 147: s = "invalid IdentOrDigitsSuffix"; break;
			case 148: s = "this symbol not expected in FieldDecl"; break;
			case 149: s = "invalid FunctionDecl"; break;
			case 150: s = "invalid FunctionDecl"; break;
			case 151: s = "invalid FunctionDecl"; break;
			case 152: s = "invalid FunctionDecl"; break;
			case 153: s = "this symbol not expected in MethodDecl"; break;
			case 154: s = "invalid MethodDecl"; break;
			case 155: s = "invalid MethodDecl"; break;
			case 156: s = "invalid FIdentType"; break;
			case 157: s = "this symbol not expected in OldSemi"; break;
			case 158: s = "invalid TypeIdentOptional"; break;
			case 159: s = "invalid TypeAndToken"; break;
			case 160: s = "this symbol not expected in IteratorSpec"; break;
			case 161: s = "invalid IteratorSpec"; break;
			case 162: s = "invalid IteratorSpec"; break;
			case 163: s = "this symbol not expected in MethodSpec"; break;
			case 164: s = "invalid MethodSpec"; break;
			case 165: s = "invalid MethodSpec"; break;
			case 166: s = "invalid FrameExpression"; break;
			case 167: s = "invalid ReferenceType"; break;
			case 168: s = "this symbol not expected in FunctionSpec"; break;
			case 169: s = "invalid FunctionSpec"; break;
			case 170: s = "invalid PossiblyWildFrameExpression"; break;
			case 171: s = "invalid PossiblyWildExpression"; break;
			case 172: s = "this symbol not expected in OneStmt"; break;
			case 173: s = "invalid OneStmt"; break;
			case 174: s = "this symbol not expected in OneStmt"; break;
			case 175: s = "invalid OneStmt"; break;
			case 176: s = "invalid AssertStmt"; break;
			case 177: s = "invalid AssumeStmt"; break;
			case 178: s = "invalid UpdateStmt"; break;
			case 179: s = "invalid UpdateStmt"; break;
			case 180: s = "invalid IfStmt"; break;
			case 181: s = "invalid IfStmt"; break;
			case 182: s = "invalid WhileStmt"; break;
			case 183: s = "invalid WhileStmt"; break;
			case 184: s = "invalid MatchStmt"; break;
			case 185: s = "invalid ForallStmt"; break;
			case 186: s = "invalid ForallStmt"; break;
			case 187: s = "this symbol not expected in ModifyStmt"; break;
			case 188: s = "invalid ModifyStmt"; break;
			case 189: s = "invalid ReturnStmt"; break;
			case 190: s = "invalid Rhs"; break;
			case 191: s = "invalid Lhs"; break;
			case 192: s = "invalid Guard"; break;
			case 193: s = "this symbol not expected in LoopSpec"; break;
			case 194: s = "this symbol not expected in LoopSpec"; break;
			case 195: s = "this symbol not expected in Invariant"; break;
			case 196: s = "invalid CalcOp"; break;
			case 197: s = "invalid EquivOp"; break;
			case 198: s = "invalid ImpliesOp"; break;
			case 199: s = "invalid ExpliesOp"; break;
			case 200: s = "invalid AndOp"; break;
			case 201: s = "invalid OrOp"; break;
			case 202: s = "invalid RelOp"; break;
			case 203: s = "invalid AddOp"; break;
			case 204: s = "invalid UnaryExpression"; break;
			case 205: s = "invalid UnaryExpression"; break;
			case 206: s = "invalid MulOp"; break;
			case 207: s = "invalid NegOp"; break;
			case 208: s = "invalid EndlessExpression"; break;
			case 209: s = "invalid Suffix"; break;
			case 210: s = "invalid Suffix"; break;
			case 211: s = "invalid Suffix"; break;
			case 212: s = "invalid DisplayExpr"; break;
			case 213: s = "invalid MultiSetExpr"; break;
			case 214: s = "invalid ConstAtomExpression"; break;
			case 215: s = "invalid Nat"; break;
			case 216: s = "invalid LambdaArrow"; break;
			case 217: s = "invalid QSep"; break;
			case 218: s = "invalid MatchExpression"; break;
			case 219: s = "invalid QuantifierGuts"; break;
			case 220: s = "invalid StmtInExpr"; break;
			case 221: s = "invalid LetExpr"; break;
			case 222: s = "invalid CasePattern"; break;
			case 223: s = "invalid Forall"; break;
			case 224: s = "invalid Exists"; break;

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