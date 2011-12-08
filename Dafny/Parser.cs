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
	public const int _arrayToken = 3;
	public const int _string = 4;
	public const int maxT = 105;

	const bool T = true;
	const bool x = false;
	const int minErrDist = 2;

	public Scanner/*!*/ scanner;
	public Errors/*!*/  errors;

	public Token/*!*/ t;    // last recognized token
	public Token/*!*/ la;   // lookahead token
	int errDist = minErrDist;

static List<ModuleDecl/*!*/> theModules;
static BuiltIns theBuiltIns;
static Expression/*!*/ dummyExpr = new LiteralExpr(Token.NoToken);
static FrameExpression/*!*/ dummyFrameExpr = new FrameExpression(dummyExpr, null);
static Statement/*!*/ dummyStmt = new ReturnStmt(Token.NoToken, null);
static Attributes.Argument/*!*/ dummyAttrArg = new Attributes.Argument(Token.NoToken, "dummyAttrArg");
static int anonymousIds = 0;
struct MemberModifiers {
  public bool IsGhost;
  public bool IsStatic;
  public bool IsUnlimited;
}
// helper routine for parsing call statements
private static Expression/*!*/ ConvertToLocal(Expression/*!*/ e)
{
Contract.Requires(e != null);
Contract.Ensures(Contract.Result<Expression>() != null);
  FieldSelectExpr fse = e as FieldSelectExpr;
  if (fse != null && fse.Obj is ImplicitThisExpr) {
    return new IdentifierExpr(fse.tok, fse.FieldName);
  }
  return e;  // cannot convert to IdentifierExpr (or is already an IdentifierExpr)
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members) from "filename"
/// and appends them in appropriate form to "modules".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string/*!*/ filename, List<ModuleDecl/*!*/>/*!*/ modules, BuiltIns builtIns) /* throws System.IO.IOException */ {
  Contract.Requires(filename != null);
  Contract.Requires(cce.NonNullElements(modules));
  string s;
  if (filename == "stdin.dfy") {
    s = Microsoft.Boogie.ParserHelper.Fill(System.Console.In, new List<string>());
    return Parse(s, filename, modules, builtIns);
  } else {
    using (System.IO.StreamReader reader = new System.IO.StreamReader(filename)) {
      s = Microsoft.Boogie.ParserHelper.Fill(reader, new List<string>());
      return Parse(s, filename, modules, builtIns);
    }
  }
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "modules".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ filename, List<ModuleDecl/*!*/>/*!*/ modules, BuiltIns builtIns) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(cce.NonNullElements(modules));
  Errors errors = new Errors();
  return Parse(s, filename, modules, builtIns, errors);
}
///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "modules".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner with the given Errors sink.
///</summary>
public static int Parse (string/*!*/ s, string/*!*/ filename, List<ModuleDecl/*!*/>/*!*/ modules, BuiltIns builtIns,
                         Errors/*!*/ errors) {
  Contract.Requires(s != null);
  Contract.Requires(filename != null);
  Contract.Requires(cce.NonNullElements(modules));
  Contract.Requires(errors != null);
  List<ModuleDecl/*!*/> oldModules = theModules;
  theModules = modules;
  BuiltIns oldBuiltIns = builtIns;
  theBuiltIns = builtIns;
  byte[]/*!*/ buffer = cce.NonNull( UTF8Encoding.Default.GetBytes(s));
  MemoryStream ms = new MemoryStream(buffer,false);
  Scanner scanner = new Scanner(ms, errors, filename);
  Parser parser = new Parser(scanner, errors);
  parser.Parse();
  theModules = oldModules;
  theBuiltIns = oldBuiltIns;
  return parser.errors.count;
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
		ClassDecl/*!*/ c; DatatypeDecl/*!*/ dt; ArbitraryTypeDecl at;
		Attributes attrs;  IToken/*!*/ id;  List<string/*!*/> theImports;
		List<MemberDecl/*!*/> membersDefaultClass = new List<MemberDecl/*!*/>();
		ModuleDecl module;
		// to support multiple files, create a default module only if theModules doesn't already contain one
		DefaultModuleDecl defaultModule = null;
		foreach (ModuleDecl mdecl in theModules) {
		  defaultModule = mdecl as DefaultModuleDecl;
		  if (defaultModule != null) { break; }
		}
		bool defaultModuleCreatedHere = false;
		if (defaultModule == null) {
		  defaultModuleCreatedHere = true;
		  defaultModule = new DefaultModuleDecl();
		}
		
		while (StartOf(1)) {
			if (la.kind == 5) {
				Get();
				attrs = null;  theImports = new List<string/*!*/>(); 
				while (la.kind == 7) {
					Attribute(ref attrs);
				}
				Ident(out id);
				if (la.kind == 6) {
					Get();
					Idents(theImports);
				}
				module = new ModuleDecl(id, id.val, theImports, attrs); 
				Expect(7);
				module.BodyStartTok = t; 
				while (la.kind == 9 || la.kind == 14 || la.kind == 20) {
					if (la.kind == 9) {
						ClassDecl(module, out c);
						module.TopLevelDecls.Add(c); 
					} else if (la.kind == 14) {
						DatatypeDecl(module, out dt);
						module.TopLevelDecls.Add(dt); 
					} else {
						ArbitraryTypeDecl(module, out at);
						module.TopLevelDecls.Add(at); 
					}
				}
				Expect(8);
				module.BodyEndTok = t;
				theModules.Add(module); 
			} else if (la.kind == 9) {
				ClassDecl(defaultModule, out c);
				defaultModule.TopLevelDecls.Add(c); 
			} else if (la.kind == 14) {
				DatatypeDecl(defaultModule, out dt);
				defaultModule.TopLevelDecls.Add(dt); 
			} else if (la.kind == 20) {
				ArbitraryTypeDecl(defaultModule, out at);
				defaultModule.TopLevelDecls.Add(at); 
			} else {
				ClassMemberDecl(membersDefaultClass, false);
			}
		}
		if (defaultModuleCreatedHere) {
		 defaultModule.TopLevelDecls.Add(new DefaultClassDecl(defaultModule, membersDefaultClass));
		 theModules.Add(defaultModule);
		} else {
		  // find the default class in the default module, then append membersDefaultClass to its member list
		  foreach (TopLevelDecl topleveldecl in defaultModule.TopLevelDecls) {
		    DefaultClassDecl defaultClass = topleveldecl as DefaultClassDecl;
		    if (defaultClass != null) {
		      defaultClass.Members.AddRange(membersDefaultClass);
		      break;
		    }
		  }
		}
		
		Expect(0);
	}

	void Attribute(ref Attributes attrs) {
		Expect(7);
		AttributeBody(ref attrs);
		Expect(8);
	}

	void Ident(out IToken/*!*/ x) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); 
		Expect(1);
		x = t; 
	}

	void Idents(List<string/*!*/>/*!*/ ids) {
		IToken/*!*/ id; 
		Ident(out id);
		ids.Add(id.val); 
		while (la.kind == 19) {
			Get();
			Ident(out id);
			ids.Add(id.val); 
		}
	}

	void ClassDecl(ModuleDecl/*!*/ module, out ClassDecl/*!*/ c) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		IToken/*!*/ idRefined;
		IToken optionalId = null;
		List<MemberDecl/*!*/> members = new List<MemberDecl/*!*/>();
		IToken bodyStart;
		
		while (!(la.kind == 0 || la.kind == 9)) {SynErr(106); Get();}
		Expect(9);
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 24) {
			GenericParameters(typeArgs);
		}
		if (la.kind == 10) {
			Get();
			Ident(out idRefined);
			optionalId = idRefined; 
		}
		Expect(7);
		bodyStart = t; 
		while (StartOf(2)) {
			ClassMemberDecl(members, true);
		}
		Expect(8);
		if (optionalId == null)
		 c = new ClassDecl(id, id.val, module, typeArgs, members, attrs);
		else
		  c = new ClassRefinementDecl(id, id.val, module, typeArgs, members, attrs, optionalId);
		c.BodyStartTok = bodyStart;
		c.BodyEndTok = t;
		
	}

	void DatatypeDecl(ModuleDecl/*!*/ module, out DatatypeDecl/*!*/ dt) {
		Contract.Requires(module != null);
		Contract.Ensures(Contract.ValueAtReturn(out dt)!=null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<DatatypeCtor/*!*/> ctors = new List<DatatypeCtor/*!*/>();
		IToken bodyStart = Token.NoToken;  // dummy assignment
		
		while (!(la.kind == 0 || la.kind == 14)) {SynErr(107); Get();}
		Expect(14);
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 24) {
			GenericParameters(typeArgs);
		}
		Expect(15);
		bodyStart = t; 
		DatatypeMemberDecl(ctors);
		while (la.kind == 16) {
			Get();
			DatatypeMemberDecl(ctors);
		}
		while (!(la.kind == 0 || la.kind == 17)) {SynErr(108); Get();}
		Expect(17);
		dt = new DatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		dt.BodyStartTok = bodyStart;
		dt.BodyEndTok = t;
		
	}

	void ArbitraryTypeDecl(ModuleDecl/*!*/ module, out ArbitraryTypeDecl at) {
		IToken/*!*/ id;
		Attributes attrs = null;
		
		Expect(20);
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		at = new ArbitraryTypeDecl(id, id.val, module, attrs); 
		while (!(la.kind == 0 || la.kind == 17)) {SynErr(109); Get();}
		Expect(17);
	}

	void ClassMemberDecl(List<MemberDecl/*!*/>/*!*/ mm, bool allowConstructors) {
		Contract.Requires(cce.NonNullElements(mm));
		Method/*!*/ m;
		Function/*!*/ f;
		MemberModifiers mmod = new MemberModifiers();
		
		while (la.kind == 11 || la.kind == 12 || la.kind == 13) {
			if (la.kind == 11) {
				Get();
				mmod.IsGhost = true; 
			} else if (la.kind == 12) {
				Get();
				mmod.IsStatic = true; 
			} else {
				Get();
				mmod.IsUnlimited = true; 
			}
		}
		if (la.kind == 18) {
			FieldDecl(mmod, mm);
		} else if (la.kind == 43) {
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (la.kind == 10 || la.kind == 26 || la.kind == 27) {
			MethodDecl(mmod, allowConstructors, out m);
			mm.Add(m); 
		} else if (la.kind == 21) {
			CouplingInvDecl(mmod, mm);
		} else SynErr(110);
	}

	void GenericParameters(List<TypeParameter/*!*/>/*!*/ typeArgs) {
		Contract.Requires(cce.NonNullElements(typeArgs));
		IToken/*!*/ id; 
		Expect(24);
		Ident(out id);
		typeArgs.Add(new TypeParameter(id, id.val)); 
		while (la.kind == 19) {
			Get();
			Ident(out id);
			typeArgs.Add(new TypeParameter(id, id.val)); 
		}
		Expect(25);
	}

	void FieldDecl(MemberModifiers mmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		IToken/*!*/ id;  Type/*!*/ ty;
		
		while (!(la.kind == 0 || la.kind == 18)) {SynErr(111); Get();}
		Expect(18);
		if (mmod.IsUnlimited) { SemErr(t, "fields cannot be declared 'unlimited'"); }
		if (mmod.IsStatic) { SemErr(t, "fields cannot be declared 'static'"); }
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		IdentType(out id, out ty);
		mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		while (la.kind == 19) {
			Get();
			IdentType(out id, out ty);
			mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		}
		while (!(la.kind == 0 || la.kind == 17)) {SynErr(112); Get();}
		Expect(17);
	}

	void FunctionDecl(MemberModifiers mmod, out Function/*!*/ f) {
		Contract.Ensures(Contract.ValueAtReturn(out f)!=null);
		Attributes attrs = null;
		IToken/*!*/ id;
		List<TypeParameter/*!*/> typeArgs = new List<TypeParameter/*!*/>();
		List<Formal/*!*/> formals = new List<Formal/*!*/>();
		Type/*!*/ returnType;
		List<Expression/*!*/> reqs = new List<Expression/*!*/>();
		List<Expression/*!*/> ens = new List<Expression/*!*/>();
		List<FrameExpression/*!*/> reads = new List<FrameExpression/*!*/>();
		List<Expression/*!*/> decreases = new List<Expression/*!*/>();
		Expression/*!*/ bb;  Expression body = null;
		bool isFunctionMethod = false;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		
		Expect(43);
		if (la.kind == 26) {
			Get();
			isFunctionMethod = true; 
		}
		if (mmod.IsGhost) { SemErr(t, "functions cannot be declared 'ghost' (they are ghost by default)"); }
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 24) {
			GenericParameters(typeArgs);
		}
		Formals(true, isFunctionMethod, formals);
		Expect(23);
		Type(out returnType);
		while (StartOf(3)) {
			FunctionSpec(reqs, reads, ens, decreases);
		}
		if (la.kind == 7) {
			FunctionBody(out bb, out bodyStart, out bodyEnd);
			body = bb; 
		}
		f = new Function(id, id.val, mmod.IsStatic, !isFunctionMethod, mmod.IsUnlimited, typeArgs, formals, returnType, reqs, reads, ens, decreases, body, attrs);
		f.BodyStartTok = bodyStart;
		f.BodyEndTok = bodyEnd;
		
	}

	void MethodDecl(MemberModifiers mmod, bool allowConstructor, out Method/*!*/ m) {
		Contract.Ensures(Contract.ValueAtReturn(out m) !=null);
		IToken/*!*/ id;
		Attributes attrs = null;
		List<TypeParameter/*!*/>/*!*/ typeArgs = new List<TypeParameter/*!*/>();
		List<Formal/*!*/> ins = new List<Formal/*!*/>();
		List<Formal/*!*/> outs = new List<Formal/*!*/>();
		List<MaybeFreeExpression/*!*/> req = new List<MaybeFreeExpression/*!*/>();
		List<FrameExpression/*!*/> mod = new List<FrameExpression/*!*/>();
		List<MaybeFreeExpression/*!*/> ens = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> dec = new List<Expression/*!*/>();
		Statement/*!*/ bb;  BlockStmt body = null;
		bool isConstructor = false;
		bool isRefinement = false;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		
		while (!(StartOf(4))) {SynErr(113); Get();}
		if (la.kind == 26) {
			Get();
		} else if (la.kind == 27) {
			Get();
			if (allowConstructor) {
			 isConstructor = true;
			} else {
			  SemErr(t, "constructors are only allowed in classes");
			}
			
		} else if (la.kind == 10) {
			Get();
			isRefinement = true; 
		} else SynErr(114);
		if (mmod.IsUnlimited) { SemErr(t, "methods cannot be declared 'unlimited'"); }
		if (isConstructor) {
		  if (mmod.IsGhost) {
		    SemErr(t, "constructors cannot be declared 'ghost'");
		  }
		  if (mmod.IsStatic) {
		    SemErr(t, "constructors cannot be declared 'static'");
		  }
		}
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 24) {
			GenericParameters(typeArgs);
		}
		Formals(true, !mmod.IsGhost, ins);
		if (la.kind == 28) {
			Get();
			if (isConstructor) { SemErr(t, "constructors cannot have out-parameters"); } 
			Formals(false, !mmod.IsGhost, outs);
		}
		while (StartOf(5)) {
			MethodSpec(req, mod, ens, dec);
		}
		if (la.kind == 7) {
			BlockStmt(out bb, out bodyStart, out bodyEnd);
			body = (BlockStmt)bb; 
		}
		if (isRefinement)
		 m = new MethodRefinement(id, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs, req, mod, ens, dec, body, attrs);
		else if (isConstructor)
		  m = new Constructor(id, id.val, typeArgs, ins, req, mod, ens, dec, body, attrs);
		else
		  m = new Method(id, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs, req, mod, ens, dec, body, attrs);
		m.BodyStartTok = bodyStart;
		m.BodyEndTok = bodyEnd;
		
	}

	void CouplingInvDecl(MemberModifiers mmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		List<IToken/*!*/> ids = new List<IToken/*!*/>();;
		IToken/*!*/ id;
		Expression/*!*/ e;
		
		Expect(21);
		if (mmod.IsUnlimited) { SemErr(t, "coupling invariants cannot be declared 'unlimited'"); }
		if (mmod.IsStatic) { SemErr(t, "coupling invariants cannot be declared 'static'"); }
		if (mmod.IsGhost) { SemErr(t, "coupling invariants cannot be declared 'ghost'"); }
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		ids.Add(id); 
		while (la.kind == 19) {
			Get();
			Ident(out id);
			ids.Add(id); 
		}
		Expect(22);
		Expression(out e);
		Expect(17);
		mm.Add(new CouplingInvariant(ids, e, attrs)); 
	}

	void DatatypeMemberDecl(List<DatatypeCtor/*!*/>/*!*/ ctors) {
		Contract.Requires(cce.NonNullElements(ctors));
		Attributes attrs = null;
		IToken/*!*/ id;
		List<Formal/*!*/> formals = new List<Formal/*!*/>();
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 34) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(34);
		if (StartOf(6)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 19) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(35);
	}

	void IdentType(out IToken/*!*/ id, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		Ident(out id);
		Expect(23);
		Type(out ty);
	}

	void Expression(out Expression/*!*/ e) {
		EquivExpression(out e);
	}

	void GIdentType(bool allowGhostKeyword, out IToken/*!*/ id, out Type/*!*/ ty, out bool isGhost) {
		Contract.Ensures(Contract.ValueAtReturn(out id)!=null);
		Contract.Ensures(Contract.ValueAtReturn(out ty)!=null);
		isGhost = false; 
		if (la.kind == 11) {
			Get();
			if (allowGhostKeyword) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
		}
		IdentType(out id, out ty);
	}

	void Type(out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out ty) != null); IToken/*!*/ tok; 
		TypeAndToken(out tok, out ty);
	}

	void LocalIdentTypeOptional(out VarDecl/*!*/ var, bool isGhost) {
		IToken/*!*/ id;  Type/*!*/ ty;  Type optType = null;
		
		Ident(out id);
		if (la.kind == 23) {
			Get();
			Type(out ty);
			optType = ty; 
		}
		var = new VarDecl(id, id.val, optType == null ? new InferredTypeProxy() : optType, isGhost); 
	}

	void IdentTypeOptional(out BoundVar/*!*/ var) {
		Contract.Ensures(Contract.ValueAtReturn(out var)!=null); IToken/*!*/ id;  Type/*!*/ ty;  Type optType = null;
		
		Ident(out id);
		if (la.kind == 23) {
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
		string name = null;  isGhost = false; 
		if (la.kind == 11) {
			Get();
			isGhost = true; 
		}
		TypeAndToken(out id, out ty);
		if (la.kind == 23) {
			Get();
			UserDefinedType udt = ty as UserDefinedType;
			if (udt != null && udt.TypeArgs.Count == 0) {
			  name = udt.Name;
			} else {
			  SemErr(id, "invalid formal-parameter name in datatype constructor");
			}
			
			Type(out ty);
		}
		if (name != null) {
		 identName = name;
		} else {
		  identName = "#" + anonymousIds++;
		}
		
	}

	void TypeAndToken(out IToken/*!*/ tok, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok)!=null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null); tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type/*!*/>/*!*/ gt;
		
		switch (la.kind) {
		case 36: {
			Get();
			tok = t; 
			break;
		}
		case 37: {
			Get();
			tok = t;  ty = new NatType(); 
			break;
		}
		case 38: {
			Get();
			tok = t;  ty = new IntType(); 
			break;
		}
		case 39: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("set type expects exactly one type argument");
			}
			ty = new SetType(gt[0]);
			
			break;
		}
		case 40: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("multiset type expects exactly one type argument");
			}
			ty = new MultiSetType(gt[0]);
			
			break;
		}
		case 41: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("seq type expects exactly one type argument");
			}
			ty = new SeqType(gt[0]);
			
			break;
		}
		case 1: case 3: case 42: {
			ReferenceType(out tok, out ty);
			break;
		}
		default: SynErr(115); break;
		}
	}

	void Formals(bool incoming, bool allowGhostKeyword, List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  bool isGhost; 
		Expect(34);
		if (la.kind == 1 || la.kind == 11) {
			GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 19) {
				Get();
				GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(35);
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false;
		
		while (!(StartOf(7))) {SynErr(116); Get();}
		if (la.kind == 29) {
			Get();
			if (StartOf(8)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 19) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			}
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(117); Get();}
			Expect(17);
		} else if (la.kind == 30 || la.kind == 31 || la.kind == 32) {
			if (la.kind == 30) {
				Get();
				isFree = true; 
			}
			if (la.kind == 31) {
				Get();
				Expression(out e);
				while (!(la.kind == 0 || la.kind == 17)) {SynErr(118); Get();}
				Expect(17);
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 32) {
				Get();
				Expression(out e);
				while (!(la.kind == 0 || la.kind == 17)) {SynErr(119); Get();}
				Expect(17);
				ens.Add(new MaybeFreeExpression(e, isFree)); 
			} else SynErr(120);
		} else if (la.kind == 33) {
			Get();
			DecreasesList(decreases, false);
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(121); Get();}
			Expect(17);
		} else SynErr(122);
	}

	void BlockStmt(out Statement/*!*/ block, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out block) != null);
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(7);
		bodyStart = t; 
		while (StartOf(9)) {
			Stmt(body);
		}
		Expect(8);
		bodyEnd = t;
		block = new BlockStmt(bodyStart, body); 
	}

	void FrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); Expression/*!*/ e;  IToken/*!*/ id;  string fieldName = null; 
		Expression(out e);
		if (la.kind == 46) {
			Get();
			Ident(out id);
			fieldName = id.val; 
		}
		fe = new FrameExpression(e, fieldName); 
	}

	void DecreasesList(List<Expression/*!*/> decreases, bool allowWildcard) {
		Expression/*!*/ e; 
		PossiblyWildExpression(out e);
		if (!allowWildcard && e is WildcardExpr) {
		 SemErr(e.tok, "'decreases *' is only allowed on loops");
		} else {
		  decreases.Add(e);
		}
		
		while (la.kind == 19) {
			Get();
			PossiblyWildExpression(out e);
			if (!allowWildcard && e is WildcardExpr) {
			 SemErr(e.tok, "'decreases *' is only allowed on loops");
			} else {
			  decreases.Add(e);
			}
			
		}
	}

	void GenericInstantiation(List<Type/*!*/>/*!*/ gt) {
		Contract.Requires(cce.NonNullElements(gt)); Type/*!*/ ty; 
		Expect(24);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 19) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(25);
	}

	void ReferenceType(out IToken/*!*/ tok, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type/*!*/>/*!*/ gt;
		
		if (la.kind == 42) {
			Get();
			tok = t;  ty = new ObjectType(); 
		} else if (la.kind == 3) {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("array type expects exactly one type argument");
			}
			int dims = 1;
			if (tok.val.Length != 5) {
			  dims = int.Parse(tok.val.Substring(5));
			}
			ty = theBuiltIns.ArrayType(tok, dims, gt[0], true);
			
		} else if (la.kind == 1) {
			Ident(out tok);
			gt = new List<Type/*!*/>(); 
			if (la.kind == 24) {
				GenericInstantiation(gt);
			}
			ty = new UserDefinedType(tok, tok.val, gt); 
		} else SynErr(123);
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(reqs)); Contract.Requires(cce.NonNullElements(reads)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		if (la.kind == 31) {
			while (!(la.kind == 0 || la.kind == 31)) {SynErr(124); Get();}
			Get();
			Expression(out e);
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(125); Get();}
			Expect(17);
			reqs.Add(e); 
		} else if (la.kind == 44) {
			Get();
			if (StartOf(10)) {
				PossiblyWildFrameExpression(out fe);
				reads.Add(fe); 
				while (la.kind == 19) {
					Get();
					PossiblyWildFrameExpression(out fe);
					reads.Add(fe); 
				}
			}
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(126); Get();}
			Expect(17);
		} else if (la.kind == 32) {
			Get();
			Expression(out e);
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(127); Get();}
			Expect(17);
			ens.Add(e); 
		} else if (la.kind == 33) {
			Get();
			DecreasesList(decreases, false);
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(128); Get();}
			Expect(17);
		} else SynErr(129);
	}

	void FunctionBody(out Expression/*!*/ e, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); e = dummyExpr; 
		Expect(7);
		bodyStart = t; 
		Expression(out e);
		Expect(8);
		bodyEnd = t; 
	}

	void PossiblyWildFrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); fe = dummyFrameExpr; 
		if (la.kind == 45) {
			Get();
			fe = new FrameExpression(new WildcardExpr(t), null); 
		} else if (StartOf(8)) {
			FrameExpression(out fe);
		} else SynErr(130);
	}

	void PossiblyWildExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 45) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(131);
	}

	void Stmt(List<Statement/*!*/>/*!*/ ss) {
		Statement/*!*/ s;
		
		OneStmt(out s);
		ss.Add(s); 
	}

	void OneStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  IToken/*!*/ id;  string label = null;
		s = dummyStmt;  /* to please the compiler */
		IToken bodyStart, bodyEnd;
		int breakCount;
		
		while (!(StartOf(11))) {SynErr(132); Get();}
		switch (la.kind) {
		case 7: {
			BlockStmt(out s, out bodyStart, out bodyEnd);
			break;
		}
		case 63: {
			AssertStmt(out s);
			break;
		}
		case 64: {
			AssumeStmt(out s);
			break;
		}
		case 65: {
			PrintStmt(out s);
			break;
		}
		case 1: case 2: case 16: case 34: case 90: case 91: case 92: case 93: case 94: case 95: case 96: {
			UpdateStmt(out s);
			break;
		}
		case 11: case 18: {
			VarDeclStatement(out s);
			break;
		}
		case 56: {
			IfStmt(out s);
			break;
		}
		case 60: {
			WhileStmt(out s);
			break;
		}
		case 62: {
			MatchStmt(out s);
			break;
		}
		case 66: {
			ParallelStmt(out s);
			break;
		}
		case 47: {
			Get();
			x = t; 
			Ident(out id);
			Expect(23);
			OneStmt(out s);
			s.Labels = new LabelNode(x, id.val, s.Labels); 
			break;
		}
		case 48: {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				Ident(out id);
				label = id.val; 
			} else if (la.kind == 17 || la.kind == 48) {
				while (la.kind == 48) {
					Get();
					breakCount++; 
				}
			} else SynErr(133);
			while (!(la.kind == 0 || la.kind == 17)) {SynErr(134); Get();}
			Expect(17);
			s = label != null ? new BreakStmt(x, label) : new BreakStmt(x, breakCount); 
			break;
		}
		case 49: {
			ReturnStmt(out s);
			break;
		}
		default: SynErr(135); break;
		}
	}

	void AssertStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ e; 
		Expect(63);
		x = t; 
		Expression(out e);
		Expect(17);
		s = new AssertStmt(x, e); 
	}

	void AssumeStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ e; 
		Expect(64);
		x = t; 
		Expression(out e);
		Expect(17);
		s = new AssumeStmt(x, e); 
	}

	void PrintStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Attributes.Argument/*!*/ arg;
		List<Attributes.Argument/*!*/> args = new List<Attributes.Argument/*!*/>();
		
		Expect(65);
		x = t; 
		AttributeArg(out arg);
		args.Add(arg); 
		while (la.kind == 19) {
			Get();
			AttributeArg(out arg);
			args.Add(arg); 
		}
		Expect(17);
		s = new PrintStmt(x, args); 
	}

	void UpdateStmt(out Statement/*!*/ s) {
		List<Expression> lhss = new List<Expression>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		Expression e;  AssignmentRhs r;
		Expression lhs0;
		IToken x;
		
		Lhs(out e);
		x = e.tok; 
		if (la.kind == 17) {
			Get();
			rhss.Add(new ExprRhs(e)); 
		} else if (la.kind == 19 || la.kind == 50) {
			lhss.Add(e);  lhs0 = e; 
			while (la.kind == 19) {
				Get();
				Lhs(out e);
				lhss.Add(e); 
			}
			Expect(50);
			x = t; 
			Rhs(out r, lhs0);
			rhss.Add(r); 
			while (la.kind == 19) {
				Get();
				Rhs(out r, lhs0);
				rhss.Add(r); 
			}
			Expect(17);
		} else if (la.kind == 23) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(136);
		s = new UpdateStmt(x, lhss, rhss); 
	}

	void VarDeclStatement(out Statement/*!*/ s) {
		IToken x = null, assignTok = null;  bool isGhost = false;
		VarDecl/*!*/ d;
		AssignmentRhs r;  IdentifierExpr lhs0;
		List<VarDecl> lhss = new List<VarDecl>();
		List<AssignmentRhs> rhss = new List<AssignmentRhs>();
		
		if (la.kind == 11) {
			Get();
			isGhost = true;  x = t; 
		}
		Expect(18);
		if (!isGhost) { x = t; } 
		LocalIdentTypeOptional(out d, isGhost);
		lhss.Add(d); 
		while (la.kind == 19) {
			Get();
			LocalIdentTypeOptional(out d, isGhost);
			lhss.Add(d); 
		}
		if (la.kind == 50) {
			Get();
			assignTok = t;
			lhs0 = new IdentifierExpr(lhss[0].Tok, lhss[0].Name);
			lhs0.Var = lhss[0];  lhs0.Type = lhss[0].OptionalType;  // resolve here
			
			Rhs(out r, lhs0);
			rhss.Add(r); 
			while (la.kind == 19) {
				Get();
				Rhs(out r, lhs0);
				rhss.Add(r); 
			}
		}
		Expect(17);
		UpdateStmt update;
		if (rhss.Count == 0) {
		  update = null;
		} else {
		  var ies = new List<Expression>();
		  foreach (var lhs in lhss) {
		    ies.Add(new AutoGhostIdentifierExpr(lhs.Tok, lhs.Name));
		  }
		  update = new UpdateStmt(assignTok, ies, rhss);
		}
		s = new VarDeclStmt(x, lhss, update);
		
	}

	void IfStmt(out Statement/*!*/ ifStmt) {
		Contract.Ensures(Contract.ValueAtReturn(out ifStmt) != null); IToken/*!*/ x;
		Expression guard;
		Statement/*!*/ thn;
		Statement/*!*/ s;
		Statement els = null;
		IToken bodyStart, bodyEnd;
		List<GuardedAlternative> alternatives;
		ifStmt = dummyStmt;  // to please the compiler
		
		Expect(56);
		x = t; 
		if (la.kind == 34) {
			Guard(out guard);
			BlockStmt(out thn, out bodyStart, out bodyEnd);
			if (la.kind == 57) {
				Get();
				if (la.kind == 56) {
					IfStmt(out s);
					els = s; 
				} else if (la.kind == 7) {
					BlockStmt(out s, out bodyStart, out bodyEnd);
					els = s; 
				} else SynErr(137);
			}
			ifStmt = new IfStmt(x, guard, thn, els); 
		} else if (la.kind == 7) {
			AlternativeBlock(out alternatives);
			ifStmt = new AlternativeStmt(x, alternatives); 
		} else SynErr(138);
	}

	void WhileStmt(out Statement/*!*/ stmt) {
		Contract.Ensures(Contract.ValueAtReturn(out stmt) != null); IToken/*!*/ x;
		Expression guard;
		List<MaybeFreeExpression/*!*/> invariants = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> decreases = new List<Expression/*!*/>();
		List<FrameExpression/*!*/> mod = null;
		Statement/*!*/ body;
		IToken bodyStart, bodyEnd;
		List<GuardedAlternative> alternatives;
		stmt = dummyStmt;  // to please the compiler
		
		Expect(60);
		x = t; 
		if (la.kind == 34) {
			Guard(out guard);
			Contract.Assume(guard == null || cce.Owner.None(guard)); 
			LoopSpec(out invariants, out decreases, out mod);
			BlockStmt(out body, out bodyStart, out bodyEnd);
			stmt = new WhileStmt(x, guard, invariants, decreases, mod, body); 
		} else if (StartOf(12)) {
			LoopSpec(out invariants, out decreases, out mod);
			AlternativeBlock(out alternatives);
			stmt = new AlternativeLoopStmt(x, invariants, decreases, mod, alternatives); 
		} else SynErr(139);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>(); 
		Expect(62);
		x = t; 
		Expression(out e);
		Expect(7);
		while (la.kind == 58) {
			CaseStatement(out c);
			cases.Add(c); 
		}
		Expect(8);
		s = new MatchStmt(x, e, cases); 
	}

	void ParallelStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		IToken/*!*/ x;
		List<BoundVar/*!*/> bvars;
		Attributes attrs;
		Expression range;
		var ens = new List<MaybeFreeExpression/*!*/>();
		bool isFree;
		Expression/*!*/ e;
		Statement/*!*/ block;
		IToken bodyStart, bodyEnd;
		
		Expect(66);
		x = t; 
		Expect(34);
		QuantifierDomain(out bvars, out attrs, out range);
		if (range == null) { range = new LiteralExpr(x, true); } 
		Expect(35);
		while (la.kind == 30 || la.kind == 32) {
			isFree = false; 
			if (la.kind == 30) {
				Get();
				isFree = true; 
			}
			Expect(32);
			Expression(out e);
			Expect(17);
			ens.Add(new MaybeFreeExpression(e, isFree)); 
		}
		BlockStmt(out block, out bodyStart, out bodyEnd);
		s = new ParallelStmt(x, bvars, attrs, range, ens, block); 
	}

	void ReturnStmt(out Statement/*!*/ s) {
		IToken returnTok = null;
		List<AssignmentRhs> rhss = null;
		AssignmentRhs r;
		
		Expect(49);
		returnTok = t; 
		if (StartOf(13)) {
			Rhs(out r, null);
			rhss = new List<AssignmentRhs>(); rhss.Add(r); 
			while (la.kind == 19) {
				Get();
				Rhs(out r, null);
				rhss.Add(r); 
			}
		}
		Expect(17);
		s = new ReturnStmt(returnTok, rhss); 
	}

	void Rhs(out AssignmentRhs r, Expression receiverForInitCall) {
		IToken/*!*/ x, newToken;  Expression/*!*/ e;
		List<Expression> ee = null;
		Type ty = null;
		CallStmt initCall = null;
		List<Expression> args;
		r = null;  // to please compiler
		
		if (la.kind == 51) {
			Get();
			newToken = t; 
			TypeAndToken(out x, out ty);
			if (la.kind == 52 || la.kind == 54) {
				if (la.kind == 52) {
					Get();
					ee = new List<Expression>(); 
					Expressions(ee);
					Expect(53);
					UserDefinedType tmp = theBuiltIns.ArrayType(x, ee.Count, new IntType(), true);
					
				} else {
					Get();
					Ident(out x);
					Expect(34);
					args = new List<Expression/*!*/>(); 
					if (StartOf(8)) {
						Expressions(args);
					}
					Expect(35);
					initCall = new CallStmt(x, new List<Expression>(),
					                       receiverForInitCall, x.val, args); 
				}
			}
			if (ee != null) {
			 r = new TypeRhs(newToken, ty, ee);
			} else {
			  r = new TypeRhs(newToken, ty, initCall);
			}
			
		} else if (la.kind == 55) {
			Get();
			x = t; 
			Expression(out e);
			r = new ExprRhs(new UnaryExpr(x, UnaryExpr.Opcode.SetChoose, e)); 
		} else if (la.kind == 45) {
			Get();
			r = new HavocRhs(t); 
		} else if (StartOf(8)) {
			Expression(out e);
			r = new ExprRhs(e); 
		} else SynErr(140);
	}

	void Lhs(out Expression e) {
		e = null;  // to please the compiler
		
		if (la.kind == 1) {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else if (StartOf(14)) {
			ConstAtomExpression(out e);
			Suffix(ref e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else SynErr(141);
	}

	void Expressions(List<Expression/*!*/>/*!*/ args) {
		Contract.Requires(cce.NonNullElements(args)); Expression/*!*/ e; 
		Expression(out e);
		args.Add(e); 
		while (la.kind == 19) {
			Get();
			Expression(out e);
			args.Add(e); 
		}
	}

	void Guard(out Expression e) {
		Expression/*!*/ ee;  e = null; 
		Expect(34);
		if (la.kind == 45) {
			Get();
			e = null; 
		} else if (StartOf(8)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(142);
		Expect(35);
	}

	void AlternativeBlock(out List<GuardedAlternative> alternatives) {
		alternatives = new List<GuardedAlternative>();
		IToken x;
		Expression e;
		List<Statement> body;
		
		Expect(7);
		while (la.kind == 58) {
			Get();
			x = t; 
			Expression(out e);
			Expect(59);
			body = new List<Statement>(); 
			while (StartOf(9)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, e, body)); 
		}
		Expect(8);
	}

	void LoopSpec(out List<MaybeFreeExpression/*!*/> invariants, out List<Expression/*!*/> decreases, out List<FrameExpression/*!*/> mod) {
		FrameExpression/*!*/ fe;
		invariants = new List<MaybeFreeExpression/*!*/>();
		MaybeFreeExpression invariant = null;
		decreases = new List<Expression/*!*/>();
		mod = null;
		
		while (StartOf(15)) {
			if (la.kind == 30 || la.kind == 61) {
				Invariant(out invariant);
				while (!(la.kind == 0 || la.kind == 17)) {SynErr(143); Get();}
				Expect(17);
				invariants.Add(invariant); 
			} else if (la.kind == 33) {
				while (!(la.kind == 0 || la.kind == 33)) {SynErr(144); Get();}
				Get();
				DecreasesList(decreases, true);
				while (!(la.kind == 0 || la.kind == 17)) {SynErr(145); Get();}
				Expect(17);
			} else {
				while (!(la.kind == 0 || la.kind == 29)) {SynErr(146); Get();}
				Get();
				mod = mod ?? new List<FrameExpression>(); 
				if (StartOf(8)) {
					FrameExpression(out fe);
					mod.Add(fe); 
					while (la.kind == 19) {
						Get();
						FrameExpression(out fe);
						mod.Add(fe); 
					}
				}
				while (!(la.kind == 0 || la.kind == 17)) {SynErr(147); Get();}
				Expect(17);
			}
		}
	}

	void Invariant(out MaybeFreeExpression/*!*/ invariant) {
		bool isFree = false; Expression/*!*/ e; invariant = null; 
		while (!(la.kind == 0 || la.kind == 30 || la.kind == 61)) {SynErr(148); Get();}
		if (la.kind == 30) {
			Get();
			isFree = true; 
		}
		Expect(61);
		Expression(out e);
		invariant = new MaybeFreeExpression(e, isFree); 
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(58);
		x = t; 
		Ident(out id);
		if (la.kind == 34) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 19) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(35);
		}
		Expect(59);
		while (StartOf(9)) {
			Stmt(body);
		}
		c = new MatchCaseStmt(x, id.val, arguments, body); 
	}

	void AttributeArg(out Attributes.Argument/*!*/ arg) {
		Contract.Ensures(Contract.ValueAtReturn(out arg) != null); Expression/*!*/ e;  arg = dummyAttrArg; 
		if (la.kind == 4) {
			Get();
			arg = new Attributes.Argument(t, t.val.Substring(1, t.val.Length-2)); 
		} else if (StartOf(8)) {
			Expression(out e);
			arg = new Attributes.Argument(t, e); 
		} else SynErr(149);
	}

	void QuantifierDomain(out List<BoundVar/*!*/> bvars, out Attributes attrs, out Expression range) {
		bvars = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		attrs = null;
		range = null;
		
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 19) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		if (la.kind == 16) {
			Get();
			Expression(out range);
		}
	}

	void EquivExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		ImpliesExpression(out e0);
		while (la.kind == 67 || la.kind == 68) {
			EquivOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Iff, e0, e1); 
		}
	}

	void ImpliesExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0);
		if (la.kind == 69 || la.kind == 70) {
			ImpliesOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
		}
	}

	void EquivOp() {
		if (la.kind == 67) {
			Get();
		} else if (la.kind == 68) {
			Get();
		} else SynErr(150);
	}

	void LogicalExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0);
		if (StartOf(16)) {
			if (la.kind == 71 || la.kind == 72) {
				AndOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				while (la.kind == 71 || la.kind == 72) {
					AndOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				}
			} else {
				OrOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				while (la.kind == 73 || la.kind == 74) {
					OrOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesOp() {
		if (la.kind == 69) {
			Get();
		} else if (la.kind == 70) {
			Get();
		} else SynErr(151);
	}

	void RelationalExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken x, firstOpTok = null;  Expression e0, e1, acc = null;  BinaryExpr.Opcode op;
		List<Expression> chain = null;
		List<BinaryExpr.Opcode> ops = null;
		int kind = 0;  // 0 ("uncommitted") indicates chain of ==, possibly with one !=
		               // 1 ("ascending")   indicates chain of ==, <, <=, possibly with one !=
		               // 2 ("descending")  indicates chain of ==, >, >=, possibly with one !=
		               // 3 ("illegal")     indicates illegal chain
		               // 4 ("disjoint")    indicates chain of disjoint set operators
		bool hasSeenNeq = false;
		
		Term(out e0);
		e = e0; 
		if (StartOf(17)) {
			RelOp(out x, out op);
			firstOpTok = x; 
			Term(out e1);
			e = new BinaryExpr(x, op, e0, e1);
			if (op == BinaryExpr.Opcode.Disjoint)
			  acc = new BinaryExpr(x, BinaryExpr.Opcode.Add, e0, e1); // accumulate first two operands.
			
			while (StartOf(17)) {
				if (chain == null) {
				 chain = new List<Expression>();
				 ops = new List<BinaryExpr.Opcode>();
				 chain.Add(e0);  ops.Add(op);  chain.Add(e1);
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
				
				RelOp(out x, out op);
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
				
				Term(out e1);
				ops.Add(op); chain.Add(e1);
				if (op == BinaryExpr.Opcode.Disjoint) {
				  e = new BinaryExpr(x, BinaryExpr.Opcode.And, e, new BinaryExpr(x, op, acc, e1));
				  acc = new BinaryExpr(x, BinaryExpr.Opcode.Add, acc, e1); //e0 has already been added.
				}
				else
				  e = new BinaryExpr(x, BinaryExpr.Opcode.And, e, new BinaryExpr(x, op, e0, e1));
				
			}
		}
		if (chain != null) {
		 e = new ChainingExpression(firstOpTok, chain, ops, e);
		}
		
	}

	void AndOp() {
		if (la.kind == 71) {
			Get();
		} else if (la.kind == 72) {
			Get();
		} else SynErr(152);
	}

	void OrOp() {
		if (la.kind == 73) {
			Get();
		} else if (la.kind == 74) {
			Get();
		} else SynErr(153);
	}

	void Term(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		Factor(out e0);
		while (la.kind == 85 || la.kind == 86) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null);
		x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/;
		IToken y;
		
		switch (la.kind) {
		case 75: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			break;
		}
		case 24: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 25: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 76: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 77: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 78: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 79: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Disjoint; 
			break;
		}
		case 80: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 81: {
			Get();
			x = t;  y = Token.NoToken; 
			if (la.kind == 80) {
				Get();
				y = t; 
			}
			if (y == Token.NoToken) {
			 SemErr(x, "invalid RelOp");
			} else if (y.pos != x.pos + 1) {
			  SemErr(x, "invalid RelOp (perhaps you intended \"!in\" with no intervening whitespace?)");
			} else {
			  x.val = "!in";
			  op = BinaryExpr.Opcode.NotIn;
			}
			
			break;
		}
		case 82: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 83: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 84: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(154); break;
		}
	}

	void Factor(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0);
		while (la.kind == 45 || la.kind == 87 || la.kind == 88) {
			MulOp(out x, out op);
			UnaryExpression(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 85) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 86) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(155);
	}

	void UnaryExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		switch (la.kind) {
		case 86: {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = new BinaryExpr(x, BinaryExpr.Opcode.Sub, new LiteralExpr(x, 0), e); 
			break;
		}
		case 81: case 89: {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.Not, e); 
			break;
		}
		case 18: case 39: case 56: case 62: case 63: case 64: case 99: case 100: case 101: case 102: {
			EndlessExpression(out e);
			break;
		}
		case 1: {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
			break;
		}
		case 7: case 52: {
			DisplayExpr(out e);
			break;
		}
		case 40: {
			MultiSetExpr(out e);
			break;
		}
		case 2: case 16: case 34: case 90: case 91: case 92: case 93: case 94: case 95: case 96: {
			ConstAtomExpression(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
			break;
		}
		default: SynErr(156); break;
		}
	}

	void MulOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 45) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 87) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 88) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(157);
	}

	void NegOp() {
		if (la.kind == 81) {
			Get();
		} else if (la.kind == 89) {
			Get();
		} else SynErr(158);
	}

	void EndlessExpression(out Expression e) {
		IToken/*!*/ x;
		Expression e0, e1;
		e = dummyExpr;
		BoundVar d;
		List<BoundVar> letVars;  List<Expression> letRHSs;
		
		switch (la.kind) {
		case 56: {
			Get();
			x = t; 
			Expression(out e);
			Expect(97);
			Expression(out e0);
			Expect(57);
			Expression(out e1);
			e = new ITEExpr(x, e, e0, e1); 
			break;
		}
		case 62: {
			MatchExpression(out e);
			break;
		}
		case 99: case 100: case 101: case 102: {
			QuantifierGuts(out e);
			break;
		}
		case 39: {
			ComprehensionExpr(out e);
			break;
		}
		case 63: {
			Get();
			x = t; 
			Expression(out e0);
			Expect(17);
			Expression(out e1);
			e = new AssertExpr(x, e0, e1); 
			break;
		}
		case 64: {
			Get();
			x = t; 
			Expression(out e0);
			Expect(17);
			Expression(out e1);
			e = new AssumeExpr(x, e0, e1); 
			break;
		}
		case 18: {
			Get();
			x = t;
			letVars = new List<BoundVar>();
			letRHSs = new List<Expression>(); 
			IdentTypeOptional(out d);
			letVars.Add(d); 
			while (la.kind == 19) {
				Get();
				IdentTypeOptional(out d);
				letVars.Add(d); 
			}
			Expect(50);
			Expression(out e);
			letRHSs.Add(e); 
			while (la.kind == 19) {
				Get();
				Expression(out e);
				letRHSs.Add(e); 
			}
			Expect(17);
			Expression(out e);
			e = new LetExpr(x, letVars, letRHSs, e); 
			break;
		}
		default: SynErr(159); break;
		}
	}

	void DottedIdentifiersAndFunction(out Expression e) {
		IToken id;  IToken openParen = null;
		List<Expression> args = null;
		List<IToken> idents = new List<IToken>();
		
		Ident(out id);
		idents.Add(id); 
		while (la.kind == 54) {
			Get();
			Ident(out id);
			idents.Add(id); 
		}
		if (la.kind == 34) {
			Get();
			openParen = t;  args = new List<Expression>(); 
			if (StartOf(8)) {
				Expressions(args);
			}
			Expect(35);
		}
		e = new IdentifierSequence(idents, openParen, args); 
	}

	void Suffix(ref Expression/*!*/ e) {
		Contract.Requires(e != null); Contract.Ensures(e!=null); IToken/*!*/ id, x;  List<Expression/*!*/>/*!*/ args;
		Expression e0 = null;  Expression e1 = null;  Expression/*!*/ ee;  bool anyDots = false;
		List<Expression> multipleIndices = null;
		bool func = false;
		
		if (la.kind == 54) {
			Get();
			Ident(out id);
			if (la.kind == 34) {
				Get();
				args = new List<Expression/*!*/>();  func = true; 
				if (StartOf(8)) {
					Expressions(args);
				}
				Expect(35);
				e = new FunctionCallExpr(id, id.val, e, args); 
			}
			if (!func) { e = new FieldSelectExpr(id, e, id.val); } 
		} else if (la.kind == 52) {
			Get();
			x = t; 
			if (StartOf(8)) {
				Expression(out ee);
				e0 = ee; 
				if (la.kind == 98) {
					Get();
					anyDots = true; 
					if (StartOf(8)) {
						Expression(out ee);
						e1 = ee; 
					}
				} else if (la.kind == 50) {
					Get();
					Expression(out ee);
					e1 = ee; 
				} else if (la.kind == 19 || la.kind == 53) {
					while (la.kind == 19) {
						Get();
						Expression(out ee);
						if (multipleIndices == null) {
						 multipleIndices = new List<Expression>();
						 multipleIndices.Add(e0);
						}
						multipleIndices.Add(ee);
						
					}
				} else SynErr(160);
			} else if (la.kind == 98) {
				Get();
				anyDots = true; 
				if (StartOf(8)) {
					Expression(out ee);
					e1 = ee; 
				}
			} else SynErr(161);
			if (multipleIndices != null) {
			 e = new MultiSelectExpr(x, e, multipleIndices);
			 // make sure an array class with this dimensionality exists
			 UserDefinedType tmp = theBuiltIns.ArrayType(x, multipleIndices.Count, new IntType(), true);
			} else {
			  if (!anyDots && e0 == null) {
			    /* a parsing error occurred */
			    e0 = dummyExpr;
			  }
			  Contract.Assert(anyDots || e0 != null);
			  if (anyDots) {
			    //Contract.Assert(e0 != null || e1 != null);
			    e = new SeqSelectExpr(x, false, e, e0, e1);
			  } else if (e1 == null) {
			    Contract.Assert(e0 != null);
			    e = new SeqSelectExpr(x, true, e, e0, null);
			  } else {
			    Contract.Assert(e0 != null);
			    e = new SeqUpdateExpr(x, e, e0, e1);
			  }
			}
			
			Expect(53);
		} else SynErr(162);
	}

	void DisplayExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		if (la.kind == 7) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements);
			Expect(8);
		} else if (la.kind == 52) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(53);
		} else SynErr(163);
	}

	void MultiSetExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x = null;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		Expect(40);
		x = t; 
		if (la.kind == 7) {
			Get();
			elements = new List<Expression/*!*/>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new MultiSetDisplayExpr(x, elements);
			Expect(8);
		} else if (la.kind == 34) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			Expression(out e);
			e = new MultiSetFormingExpr(x, e); 
			Expect(35);
		} else if (StartOf(18)) {
			SemErr("multiset must be followed by multiset literal or expression to coerce in parentheses."); 
		} else SynErr(164);
	}

	void ConstAtomExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;
		e = dummyExpr;
		
		switch (la.kind) {
		case 90: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 91: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 92: {
			Get();
			e = new LiteralExpr(t); 
			break;
		}
		case 2: {
			Nat(out n);
			e = new LiteralExpr(t, n); 
			break;
		}
		case 93: {
			Get();
			e = new ThisExpr(t); 
			break;
		}
		case 94: {
			Get();
			x = t; 
			Expect(34);
			Expression(out e);
			Expect(35);
			e = new FreshExpr(x, e); 
			break;
		}
		case 95: {
			Get();
			x = t; 
			Expect(34);
			Expression(out e);
			Expect(35);
			e = new AllocatedExpr(x, e); 
			break;
		}
		case 96: {
			Get();
			x = t; 
			Expect(34);
			Expression(out e);
			Expect(35);
			e = new OldExpr(x, e); 
			break;
		}
		case 16: {
			Get();
			x = t; 
			Expression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.SeqLength, e); 
			Expect(16);
			break;
		}
		case 34: {
			Get();
			x = t; 
			Expression(out e);
			e = new ParensExpression(x, e); 
			Expect(35);
			break;
		}
		default: SynErr(165); break;
		}
	}

	void Nat(out BigInteger n) {
		Expect(2);
		try {
		 n = BigInteger.Parse(t.val);
		} catch (System.FormatException) {
		  SemErr("incorrectly formatted number");
		  n = BigInteger.Zero;
		}
		
	}

	void MatchExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  MatchCaseExpr/*!*/ c;
		List<MatchCaseExpr/*!*/> cases = new List<MatchCaseExpr/*!*/>();
		
		Expect(62);
		x = t; 
		Expression(out e);
		while (la.kind == 58) {
			CaseExpression(out c);
			cases.Add(c); 
		}
		e = new MatchExpr(x, e, cases); 
	}

	void QuantifierGuts(out Expression/*!*/ q) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		List<BoundVar/*!*/> bvars;
		Attributes attrs;
		Expression range;
		Expression/*!*/ body;
		
		if (la.kind == 99 || la.kind == 100) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 101 || la.kind == 102) {
			Exists();
			x = t; 
		} else SynErr(166);
		QuantifierDomain(out bvars, out attrs, out range);
		QSep();
		Expression(out body);
		if (univ) {
		 q = new ForallExpr(x, bvars, range, body, attrs);
		} else {
		  q = new ExistsExpr(x, bvars, range, body, attrs);
		}
		
	}

	void ComprehensionExpr(out Expression/*!*/ q) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null);
		IToken/*!*/ x = Token.NoToken;
		BoundVar/*!*/ bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar/*!*/>();
		Expression/*!*/ range;
		Expression body = null;
		
		Expect(39);
		x = t; 
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 19) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		Expect(16);
		Expression(out range);
		if (la.kind == 103 || la.kind == 104) {
			QSep();
			Expression(out body);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(x, bvars, range, body);
		
	}

	void CaseExpression(out MatchCaseExpr/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		BoundVar/*!*/ bv;
		Expression/*!*/ body;
		
		Expect(58);
		x = t; 
		Ident(out id);
		if (la.kind == 34) {
			Get();
			IdentTypeOptional(out bv);
			arguments.Add(bv); 
			while (la.kind == 19) {
				Get();
				IdentTypeOptional(out bv);
				arguments.Add(bv); 
			}
			Expect(35);
		}
		Expect(59);
		Expression(out body);
		c = new MatchCaseExpr(x, id.val, arguments, body); 
	}

	void Forall() {
		if (la.kind == 99) {
			Get();
		} else if (la.kind == 100) {
			Get();
		} else SynErr(167);
	}

	void Exists() {
		if (la.kind == 101) {
			Get();
		} else if (la.kind == 102) {
			Get();
		} else SynErr(168);
	}

	void QSep() {
		if (la.kind == 103) {
			Get();
		} else if (la.kind == 104) {
			Get();
		} else SynErr(169);
	}

	void AttributeBody(ref Attributes attrs) {
		string aName;
		List<Attributes.Argument/*!*/> aArgs = new List<Attributes.Argument/*!*/>();
		Attributes.Argument/*!*/ aArg;
		
		Expect(23);
		Expect(1);
		aName = t.val; 
		if (StartOf(19)) {
			AttributeArg(out aArg);
			aArgs.Add(aArg); 
			while (la.kind == 19) {
				Get();
				AttributeArg(out aArg);
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
	}

	static readonly bool[,]/*!*/ set = {
		{T,T,T,x, x,x,x,T, x,T,T,T, x,x,T,x, T,T,T,x, x,x,x,x, x,x,T,T, x,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, T,x,x,x, T,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,T,x,x, x,T,T,T, T,T,T,x, x,x,T,x, T,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,T,x, x,T,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,x,T, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,T, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, T,x,x,x, T,x,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,T, T,x,x,x, x,T,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x},
		{T,T,T,x, x,x,x,T, x,x,x,T, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,x,x, x,x,x,x, T,x,x,x, T,x,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,T, T,x,x,x, x,T,x,x, x,x,x,T, T,x,x,T, T,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x},
		{x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, T,T,x,T, x,x,x,x, T,T,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,T,x, x,x,T,x, x,T,x,x, x,T,T,T, x,x,x,x, x,x,x,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,T,T,x, x,x,x,T, T,x,x},
		{x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, T,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x}

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
			case 3: s = "arrayToken expected"; break;
			case 4: s = "string expected"; break;
			case 5: s = "\"module\" expected"; break;
			case 6: s = "\"imports\" expected"; break;
			case 7: s = "\"{\" expected"; break;
			case 8: s = "\"}\" expected"; break;
			case 9: s = "\"class\" expected"; break;
			case 10: s = "\"refines\" expected"; break;
			case 11: s = "\"ghost\" expected"; break;
			case 12: s = "\"static\" expected"; break;
			case 13: s = "\"unlimited\" expected"; break;
			case 14: s = "\"datatype\" expected"; break;
			case 15: s = "\"=\" expected"; break;
			case 16: s = "\"|\" expected"; break;
			case 17: s = "\";\" expected"; break;
			case 18: s = "\"var\" expected"; break;
			case 19: s = "\",\" expected"; break;
			case 20: s = "\"type\" expected"; break;
			case 21: s = "\"replaces\" expected"; break;
			case 22: s = "\"by\" expected"; break;
			case 23: s = "\":\" expected"; break;
			case 24: s = "\"<\" expected"; break;
			case 25: s = "\">\" expected"; break;
			case 26: s = "\"method\" expected"; break;
			case 27: s = "\"constructor\" expected"; break;
			case 28: s = "\"returns\" expected"; break;
			case 29: s = "\"modifies\" expected"; break;
			case 30: s = "\"free\" expected"; break;
			case 31: s = "\"requires\" expected"; break;
			case 32: s = "\"ensures\" expected"; break;
			case 33: s = "\"decreases\" expected"; break;
			case 34: s = "\"(\" expected"; break;
			case 35: s = "\")\" expected"; break;
			case 36: s = "\"bool\" expected"; break;
			case 37: s = "\"nat\" expected"; break;
			case 38: s = "\"int\" expected"; break;
			case 39: s = "\"set\" expected"; break;
			case 40: s = "\"multiset\" expected"; break;
			case 41: s = "\"seq\" expected"; break;
			case 42: s = "\"object\" expected"; break;
			case 43: s = "\"function\" expected"; break;
			case 44: s = "\"reads\" expected"; break;
			case 45: s = "\"*\" expected"; break;
			case 46: s = "\"`\" expected"; break;
			case 47: s = "\"label\" expected"; break;
			case 48: s = "\"break\" expected"; break;
			case 49: s = "\"return\" expected"; break;
			case 50: s = "\":=\" expected"; break;
			case 51: s = "\"new\" expected"; break;
			case 52: s = "\"[\" expected"; break;
			case 53: s = "\"]\" expected"; break;
			case 54: s = "\".\" expected"; break;
			case 55: s = "\"choose\" expected"; break;
			case 56: s = "\"if\" expected"; break;
			case 57: s = "\"else\" expected"; break;
			case 58: s = "\"case\" expected"; break;
			case 59: s = "\"=>\" expected"; break;
			case 60: s = "\"while\" expected"; break;
			case 61: s = "\"invariant\" expected"; break;
			case 62: s = "\"match\" expected"; break;
			case 63: s = "\"assert\" expected"; break;
			case 64: s = "\"assume\" expected"; break;
			case 65: s = "\"print\" expected"; break;
			case 66: s = "\"parallel\" expected"; break;
			case 67: s = "\"<==>\" expected"; break;
			case 68: s = "\"\\u21d4\" expected"; break;
			case 69: s = "\"==>\" expected"; break;
			case 70: s = "\"\\u21d2\" expected"; break;
			case 71: s = "\"&&\" expected"; break;
			case 72: s = "\"\\u2227\" expected"; break;
			case 73: s = "\"||\" expected"; break;
			case 74: s = "\"\\u2228\" expected"; break;
			case 75: s = "\"==\" expected"; break;
			case 76: s = "\"<=\" expected"; break;
			case 77: s = "\">=\" expected"; break;
			case 78: s = "\"!=\" expected"; break;
			case 79: s = "\"!!\" expected"; break;
			case 80: s = "\"in\" expected"; break;
			case 81: s = "\"!\" expected"; break;
			case 82: s = "\"\\u2260\" expected"; break;
			case 83: s = "\"\\u2264\" expected"; break;
			case 84: s = "\"\\u2265\" expected"; break;
			case 85: s = "\"+\" expected"; break;
			case 86: s = "\"-\" expected"; break;
			case 87: s = "\"/\" expected"; break;
			case 88: s = "\"%\" expected"; break;
			case 89: s = "\"\\u00ac\" expected"; break;
			case 90: s = "\"false\" expected"; break;
			case 91: s = "\"true\" expected"; break;
			case 92: s = "\"null\" expected"; break;
			case 93: s = "\"this\" expected"; break;
			case 94: s = "\"fresh\" expected"; break;
			case 95: s = "\"allocated\" expected"; break;
			case 96: s = "\"old\" expected"; break;
			case 97: s = "\"then\" expected"; break;
			case 98: s = "\"..\" expected"; break;
			case 99: s = "\"forall\" expected"; break;
			case 100: s = "\"\\u2200\" expected"; break;
			case 101: s = "\"exists\" expected"; break;
			case 102: s = "\"\\u2203\" expected"; break;
			case 103: s = "\"::\" expected"; break;
			case 104: s = "\"\\u2022\" expected"; break;
			case 105: s = "??? expected"; break;
			case 106: s = "this symbol not expected in ClassDecl"; break;
			case 107: s = "this symbol not expected in DatatypeDecl"; break;
			case 108: s = "this symbol not expected in DatatypeDecl"; break;
			case 109: s = "this symbol not expected in ArbitraryTypeDecl"; break;
			case 110: s = "invalid ClassMemberDecl"; break;
			case 111: s = "this symbol not expected in FieldDecl"; break;
			case 112: s = "this symbol not expected in FieldDecl"; break;
			case 113: s = "this symbol not expected in MethodDecl"; break;
			case 114: s = "invalid MethodDecl"; break;
			case 115: s = "invalid TypeAndToken"; break;
			case 116: s = "this symbol not expected in MethodSpec"; break;
			case 117: s = "this symbol not expected in MethodSpec"; break;
			case 118: s = "this symbol not expected in MethodSpec"; break;
			case 119: s = "this symbol not expected in MethodSpec"; break;
			case 120: s = "invalid MethodSpec"; break;
			case 121: s = "this symbol not expected in MethodSpec"; break;
			case 122: s = "invalid MethodSpec"; break;
			case 123: s = "invalid ReferenceType"; break;
			case 124: s = "this symbol not expected in FunctionSpec"; break;
			case 125: s = "this symbol not expected in FunctionSpec"; break;
			case 126: s = "this symbol not expected in FunctionSpec"; break;
			case 127: s = "this symbol not expected in FunctionSpec"; break;
			case 128: s = "this symbol not expected in FunctionSpec"; break;
			case 129: s = "invalid FunctionSpec"; break;
			case 130: s = "invalid PossiblyWildFrameExpression"; break;
			case 131: s = "invalid PossiblyWildExpression"; break;
			case 132: s = "this symbol not expected in OneStmt"; break;
			case 133: s = "invalid OneStmt"; break;
			case 134: s = "this symbol not expected in OneStmt"; break;
			case 135: s = "invalid OneStmt"; break;
			case 136: s = "invalid UpdateStmt"; break;
			case 137: s = "invalid IfStmt"; break;
			case 138: s = "invalid IfStmt"; break;
			case 139: s = "invalid WhileStmt"; break;
			case 140: s = "invalid Rhs"; break;
			case 141: s = "invalid Lhs"; break;
			case 142: s = "invalid Guard"; break;
			case 143: s = "this symbol not expected in LoopSpec"; break;
			case 144: s = "this symbol not expected in LoopSpec"; break;
			case 145: s = "this symbol not expected in LoopSpec"; break;
			case 146: s = "this symbol not expected in LoopSpec"; break;
			case 147: s = "this symbol not expected in LoopSpec"; break;
			case 148: s = "this symbol not expected in Invariant"; break;
			case 149: s = "invalid AttributeArg"; break;
			case 150: s = "invalid EquivOp"; break;
			case 151: s = "invalid ImpliesOp"; break;
			case 152: s = "invalid AndOp"; break;
			case 153: s = "invalid OrOp"; break;
			case 154: s = "invalid RelOp"; break;
			case 155: s = "invalid AddOp"; break;
			case 156: s = "invalid UnaryExpression"; break;
			case 157: s = "invalid MulOp"; break;
			case 158: s = "invalid NegOp"; break;
			case 159: s = "invalid EndlessExpression"; break;
			case 160: s = "invalid Suffix"; break;
			case 161: s = "invalid Suffix"; break;
			case 162: s = "invalid Suffix"; break;
			case 163: s = "invalid DisplayExpr"; break;
			case 164: s = "invalid MultiSetExpr"; break;
			case 165: s = "invalid ConstAtomExpression"; break;
			case 166: s = "invalid QuantifierGuts"; break;
			case 167: s = "invalid Forall"; break;
			case 168: s = "invalid Exists"; break;
			case 169: s = "invalid QSep"; break;

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

	public virtual void Warning(string filename, int line, int col, string msg) {
		Contract.Requires(msg != null);
		errorStream.WriteLine(warningMsgFormat, filename, line, col, msg);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}

}