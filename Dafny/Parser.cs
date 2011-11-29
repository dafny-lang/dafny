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
	public const int maxT = 104;

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
static Attributes.Argument/*!*/ dummyAttrArg = new Attributes.Argument("dummyAttrArg");
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
		ClassDecl/*!*/ c; DatatypeDecl/*!*/ dt;
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
				while (la.kind == 9 || la.kind == 14) {
					if (la.kind == 9) {
						ClassDecl(module, out c);
						module.TopLevelDecls.Add(c); 
					} else {
						DatatypeDecl(module, out dt);
						module.TopLevelDecls.Add(dt); 
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
		
		Expect(9);
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 23) {
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
		
		Expect(14);
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 23) {
			GenericParameters(typeArgs);
		}
		Expect(15);
		bodyStart = t; 
		DatatypeMemberDecl(ctors);
		while (la.kind == 16) {
			Get();
			DatatypeMemberDecl(ctors);
		}
		Expect(17);
		dt = new DatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		dt.BodyStartTok = bodyStart;
		dt.BodyEndTok = t;
		
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
		} else if (la.kind == 41) {
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (la.kind == 10 || la.kind == 25 || la.kind == 26) {
			MethodDecl(mmod, allowConstructors, out m);
			mm.Add(m); 
		} else if (la.kind == 20) {
			CouplingInvDecl(mmod, mm);
		} else SynErr(105);
	}

	void GenericParameters(List<TypeParameter/*!*/>/*!*/ typeArgs) {
		Contract.Requires(cce.NonNullElements(typeArgs));
		IToken/*!*/ id; 
		Expect(23);
		Ident(out id);
		typeArgs.Add(new TypeParameter(id, id.val)); 
		while (la.kind == 19) {
			Get();
			Ident(out id);
			typeArgs.Add(new TypeParameter(id, id.val)); 
		}
		Expect(24);
	}

	void FieldDecl(MemberModifiers mmod, List<MemberDecl/*!*/>/*!*/ mm) {
		Contract.Requires(cce.NonNullElements(mm));
		Attributes attrs = null;
		IToken/*!*/ id;  Type/*!*/ ty;
		
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
		
		Expect(41);
		if (la.kind == 25) {
			Get();
			isFunctionMethod = true; 
		}
		if (mmod.IsGhost) { SemErr(t, "functions cannot be declared 'ghost' (they are ghost by default)"); }
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 23) {
			GenericParameters(typeArgs);
		}
		Formals(true, isFunctionMethod, formals);
		Expect(22);
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
		
		if (la.kind == 25) {
			Get();
		} else if (la.kind == 26) {
			Get();
			if (allowConstructor) {
			 isConstructor = true;
			} else {
			  SemErr(t, "constructors are only allowed in classes");
			}
			
		} else if (la.kind == 10) {
			Get();
			isRefinement = true; 
		} else SynErr(106);
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
		if (la.kind == 23) {
			GenericParameters(typeArgs);
		}
		Formals(true, !mmod.IsGhost, ins);
		if (la.kind == 27) {
			Get();
			if (isConstructor) { SemErr(t, "constructors cannot have out-parameters"); } 
			Formals(false, !mmod.IsGhost, outs);
		}
		while (StartOf(4)) {
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
		
		Expect(20);
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
		Expect(21);
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
		if (la.kind == 33) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(33);
		if (StartOf(5)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 19) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(34);
	}

	void IdentType(out IToken/*!*/ id, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out id) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		Ident(out id);
		Expect(22);
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
		if (la.kind == 22) {
			Get();
			Type(out ty);
			optType = ty; 
		}
		var = new VarDecl(id, id.val, optType == null ? new InferredTypeProxy() : optType, isGhost); 
	}

	void IdentTypeOptional(out BoundVar/*!*/ var) {
		Contract.Ensures(Contract.ValueAtReturn(out var)!=null); IToken/*!*/ id;  Type/*!*/ ty;  Type optType = null;
		
		Ident(out id);
		if (la.kind == 22) {
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
		if (la.kind == 22) {
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
		case 35: {
			Get();
			tok = t; 
			break;
		}
		case 36: {
			Get();
			tok = t;  ty = new NatType(); 
			break;
		}
		case 37: {
			Get();
			tok = t;  ty = new IntType(); 
			break;
		}
		case 38: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("set type expects exactly one type argument");
			}
			ty = new SetType(gt[0]);
			
			break;
		}
		case 39: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("seq type expects exactly one type argument");
			}
			ty = new SeqType(gt[0]);
			
			break;
		}
		case 1: case 3: case 40: {
			ReferenceType(out tok, out ty);
			break;
		}
		default: SynErr(107); break;
		}
	}

	void Formals(bool incoming, bool allowGhostKeyword, List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  bool isGhost; 
		Expect(33);
		if (la.kind == 1 || la.kind == 11) {
			GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 19) {
				Get();
				GIdentType(allowGhostKeyword, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(34);
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false;
		
		if (la.kind == 28) {
			Get();
			if (StartOf(6)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 19) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			}
			Expect(17);
		} else if (la.kind == 29 || la.kind == 30 || la.kind == 31) {
			if (la.kind == 29) {
				Get();
				isFree = true; 
			}
			if (la.kind == 30) {
				Get();
				Expression(out e);
				Expect(17);
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 31) {
				Get();
				Expression(out e);
				Expect(17);
				ens.Add(new MaybeFreeExpression(e, isFree)); 
			} else SynErr(108);
		} else if (la.kind == 32) {
			Get();
			DecreasesList(decreases, false);
			Expect(17);
		} else SynErr(109);
	}

	void BlockStmt(out Statement/*!*/ block, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out block) != null);
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(7);
		bodyStart = t; 
		while (StartOf(7)) {
			Stmt(body);
		}
		Expect(8);
		bodyEnd = t;
		block = new BlockStmt(bodyStart, body); 
	}

	void FrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); Expression/*!*/ e;  IToken/*!*/ id;  string fieldName = null; 
		Expression(out e);
		if (la.kind == 44) {
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
		Expect(23);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 19) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(24);
	}

	void ReferenceType(out IToken/*!*/ tok, out Type/*!*/ ty) {
		Contract.Ensures(Contract.ValueAtReturn(out tok) != null); Contract.Ensures(Contract.ValueAtReturn(out ty) != null);
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type/*!*/>/*!*/ gt;
		
		if (la.kind == 40) {
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
			if (la.kind == 23) {
				GenericInstantiation(gt);
			}
			ty = new UserDefinedType(tok, tok.val, gt); 
		} else SynErr(110);
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(reqs)); Contract.Requires(cce.NonNullElements(reads)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		if (la.kind == 30) {
			Get();
			Expression(out e);
			Expect(17);
			reqs.Add(e); 
		} else if (la.kind == 42) {
			Get();
			if (StartOf(8)) {
				PossiblyWildFrameExpression(out fe);
				reads.Add(fe); 
				while (la.kind == 19) {
					Get();
					PossiblyWildFrameExpression(out fe);
					reads.Add(fe); 
				}
			}
			Expect(17);
		} else if (la.kind == 31) {
			Get();
			Expression(out e);
			Expect(17);
			ens.Add(e); 
		} else if (la.kind == 32) {
			Get();
			DecreasesList(decreases, false);
			Expect(17);
		} else SynErr(111);
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
		if (la.kind == 43) {
			Get();
			fe = new FrameExpression(new WildcardExpr(t), null); 
		} else if (StartOf(6)) {
			FrameExpression(out fe);
		} else SynErr(112);
	}

	void PossiblyWildExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 43) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(6)) {
			Expression(out e);
		} else SynErr(113);
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
		case 1: case 2: case 16: case 33: case 89: case 90: case 91: case 92: case 93: case 94: case 95: {
			UpdateStmt(out s);
			break;
		}
		case 11: case 18: {
			VarDeclStatement(out s);
			break;
		}
		case 54: {
			IfStmt(out s);
			break;
		}
		case 58: {
			WhileStmt(out s);
			break;
		}
		case 60: {
			MatchStmt(out s);
			break;
		}
		case 61: {
			ForeachStmt(out s);
			break;
		}
		case 45: {
			Get();
			x = t; 
			Ident(out id);
			Expect(22);
			OneStmt(out s);
			s.Labels = new LabelNode(x, id.val, s.Labels); 
			break;
		}
		case 46: {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				Ident(out id);
				label = id.val; 
			} else if (la.kind == 17 || la.kind == 46) {
				while (la.kind == 46) {
					Get();
					breakCount++; 
				}
			} else SynErr(114);
			Expect(17);
			s = label != null ? new BreakStmt(x, label) : new BreakStmt(x, breakCount); 
			break;
		}
		case 47: {
			ReturnStmt(out s);
			break;
		}
		default: SynErr(115); break;
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
		} else if (la.kind == 19 || la.kind == 48) {
			lhss.Add(e);  lhs0 = e; 
			while (la.kind == 19) {
				Get();
				Lhs(out e);
				lhss.Add(e); 
			}
			Expect(48);
			x = t; 
			Rhs(out r, lhs0);
			rhss.Add(r); 
			while (la.kind == 19) {
				Get();
				Rhs(out r, lhs0);
				rhss.Add(r); 
			}
			Expect(17);
		} else if (la.kind == 22) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(116);
		s = new UpdateStmt(x, lhss, rhss); 
	}

	void VarDeclStatement(out Statement/*!*/ s) {
		IToken x = null, assignTok = null;  bool isGhost = false;
		VarDecl/*!*/ d;
		AssignmentRhs r;  Expression lhs0;
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
		if (la.kind == 48) {
			Get();
			assignTok = t;  lhs0 = new IdentifierExpr(lhss[0].Tok, lhss[0].Name); 
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
		
		Expect(54);
		x = t; 
		if (la.kind == 33) {
			Guard(out guard);
			BlockStmt(out thn, out bodyStart, out bodyEnd);
			if (la.kind == 55) {
				Get();
				if (la.kind == 54) {
					IfStmt(out s);
					els = s; 
				} else if (la.kind == 7) {
					BlockStmt(out s, out bodyStart, out bodyEnd);
					els = s; 
				} else SynErr(117);
			}
			ifStmt = new IfStmt(x, guard, thn, els); 
		} else if (la.kind == 7) {
			AlternativeBlock(out alternatives);
			ifStmt = new AlternativeStmt(x, alternatives); 
		} else SynErr(118);
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
		
		Expect(58);
		x = t; 
		if (la.kind == 33) {
			Guard(out guard);
			Contract.Assume(guard == null || cce.Owner.None(guard)); 
			LoopSpec(out invariants, out decreases, out mod);
			BlockStmt(out body, out bodyStart, out bodyEnd);
			stmt = new WhileStmt(x, guard, invariants, decreases, mod, body); 
		} else if (StartOf(9)) {
			LoopSpec(out invariants, out decreases, out mod);
			AlternativeBlock(out alternatives);
			stmt = new AlternativeLoopStmt(x, invariants, decreases, mod, alternatives); 
		} else SynErr(119);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>(); 
		Expect(60);
		x = t; 
		Expression(out e);
		Expect(7);
		while (la.kind == 56) {
			CaseStatement(out c);
			cases.Add(c); 
		}
		Expect(8);
		s = new MatchStmt(x, e, cases); 
	}

	void ForeachStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		IToken/*!*/ x, boundVar;
		Type/*!*/ ty;
		Expression/*!*/ collection;
		Expression/*!*/ range;
		List<PredicateStmt/*!*/> bodyPrefix = new List<PredicateStmt/*!*/>();
		Statement bodyAssign = null;
		
		Expect(61);
		x = t;
		range = new LiteralExpr(x, true);
		ty = new InferredTypeProxy();
		
		Expect(33);
		Ident(out boundVar);
		if (la.kind == 22) {
			Get();
			Type(out ty);
		}
		Expect(62);
		Expression(out collection);
		if (la.kind == 16) {
			Get();
			Expression(out range);
		}
		Expect(34);
		Expect(7);
		while (la.kind == 63 || la.kind == 64) {
			if (la.kind == 63) {
				AssertStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			} else {
				AssumeStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			}
		}
		UpdateStmt(out s);
		bodyAssign = s; 
		Expect(8);
		if (bodyAssign != null) {
		 s = new ForeachStmt(x, new BoundVar(boundVar, boundVar.val, ty), collection, range, bodyPrefix, bodyAssign);
		} else {
		  s = dummyStmt;  // some error occurred in parsing the bodyAssign
		}
		
	}

	void ReturnStmt(out Statement/*!*/ s) {
		IToken returnTok = null;
		List<AssignmentRhs> rhss = null;
		AssignmentRhs r;
		
		Expect(47);
		returnTok = t; 
		if (StartOf(10)) {
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
		
		if (la.kind == 49) {
			Get();
			newToken = t; 
			TypeAndToken(out x, out ty);
			if (la.kind == 50 || la.kind == 52) {
				if (la.kind == 50) {
					Get();
					ee = new List<Expression>(); 
					Expressions(ee);
					Expect(51);
					UserDefinedType tmp = theBuiltIns.ArrayType(x, ee.Count, new IntType(), true);
					
				} else {
					Get();
					Ident(out x);
					Expect(33);
					args = new List<Expression/*!*/>(); 
					if (StartOf(6)) {
						Expressions(args);
					}
					Expect(34);
					initCall = new CallStmt(x, new List<Expression>(),
					                       receiverForInitCall, x.val, args); 
				}
			}
			if (ee != null) {
			 r = new TypeRhs(newToken, ty, ee);
			} else {
			  r = new TypeRhs(newToken, ty, initCall);
			}
			
		} else if (la.kind == 53) {
			Get();
			x = t; 
			Expression(out e);
			r = new ExprRhs(new UnaryExpr(x, UnaryExpr.Opcode.SetChoose, e)); 
		} else if (la.kind == 43) {
			Get();
			r = new HavocRhs(t); 
		} else if (StartOf(6)) {
			Expression(out e);
			r = new ExprRhs(e); 
		} else SynErr(120);
	}

	void Lhs(out Expression e) {
		e = null;  // to please the compiler
		
		if (la.kind == 1) {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 50 || la.kind == 52) {
				Suffix(ref e);
			}
		} else if (StartOf(11)) {
			ConstAtomExpression(out e);
			Suffix(ref e);
			while (la.kind == 50 || la.kind == 52) {
				Suffix(ref e);
			}
		} else SynErr(121);
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
		Expect(33);
		if (la.kind == 43) {
			Get();
			e = null; 
		} else if (StartOf(6)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(122);
		Expect(34);
	}

	void AlternativeBlock(out List<GuardedAlternative> alternatives) {
		alternatives = new List<GuardedAlternative>();
		IToken x;
		Expression e;
		List<Statement> body;
		
		Expect(7);
		while (la.kind == 56) {
			Get();
			x = t; 
			Expression(out e);
			Expect(57);
			body = new List<Statement>(); 
			while (StartOf(7)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, e, body)); 
		}
		Expect(8);
	}

	void LoopSpec(out List<MaybeFreeExpression/*!*/> invariants, out List<Expression/*!*/> decreases, out List<FrameExpression/*!*/> mod) {
		bool isFree;  Expression/*!*/ e; FrameExpression/*!*/ fe;
		invariants = new List<MaybeFreeExpression/*!*/>();
		decreases = new List<Expression/*!*/>();
		mod = null;
		
		while (StartOf(12)) {
			if (la.kind == 29 || la.kind == 59) {
				isFree = false; 
				if (la.kind == 29) {
					Get();
					isFree = true; 
				}
				Expect(59);
				Expression(out e);
				invariants.Add(new MaybeFreeExpression(e, isFree)); 
				Expect(17);
			} else if (la.kind == 32) {
				Get();
				DecreasesList(decreases, true);
				Expect(17);
			} else {
				Get();
				mod = mod ?? new List<FrameExpression>(); 
				if (StartOf(6)) {
					FrameExpression(out fe);
					mod.Add(fe); 
					while (la.kind == 19) {
						Get();
						FrameExpression(out fe);
						mod.Add(fe); 
					}
				}
				Expect(17);
			}
		}
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id, arg;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(56);
		x = t; 
		Ident(out id);
		if (la.kind == 33) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			while (la.kind == 19) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			}
			Expect(34);
		}
		Expect(57);
		while (StartOf(7)) {
			Stmt(body);
		}
		c = new MatchCaseStmt(x, id.val, arguments, body); 
	}

	void AttributeArg(out Attributes.Argument/*!*/ arg) {
		Contract.Ensures(Contract.ValueAtReturn(out arg) != null); Expression/*!*/ e;  arg = dummyAttrArg; 
		if (la.kind == 4) {
			Get();
			arg = new Attributes.Argument(t.val.Substring(1, t.val.Length-2)); 
		} else if (StartOf(6)) {
			Expression(out e);
			arg = new Attributes.Argument(e); 
		} else SynErr(123);
	}

	void EquivExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		ImpliesExpression(out e0);
		while (la.kind == 66 || la.kind == 67) {
			EquivOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Iff, e0, e1); 
		}
	}

	void ImpliesExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		LogicalExpression(out e0);
		if (la.kind == 68 || la.kind == 69) {
			ImpliesOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
		}
	}

	void EquivOp() {
		if (la.kind == 66) {
			Get();
		} else if (la.kind == 67) {
			Get();
		} else SynErr(124);
	}

	void LogicalExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0);
		if (StartOf(13)) {
			if (la.kind == 70 || la.kind == 71) {
				AndOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				while (la.kind == 70 || la.kind == 71) {
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
				while (la.kind == 72 || la.kind == 73) {
					OrOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesOp() {
		if (la.kind == 68) {
			Get();
		} else if (la.kind == 69) {
			Get();
		} else SynErr(125);
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
		if (StartOf(14)) {
			RelOp(out x, out op);
			firstOpTok = x; 
			Term(out e1);
			e = new BinaryExpr(x, op, e0, e1);
			if (op == BinaryExpr.Opcode.Disjoint)
			  acc = new BinaryExpr(x, BinaryExpr.Opcode.Add, e0, e1); // accumulate first two operands.
			
			while (StartOf(14)) {
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
		if (la.kind == 70) {
			Get();
		} else if (la.kind == 71) {
			Get();
		} else SynErr(126);
	}

	void OrOp() {
		if (la.kind == 72) {
			Get();
		} else if (la.kind == 73) {
			Get();
		} else SynErr(127);
	}

	void Term(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		Factor(out e0);
		while (la.kind == 83 || la.kind == 84) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		switch (la.kind) {
		case 74: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			break;
		}
		case 23: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 24: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 75: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 76: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 77: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 78: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Disjoint; 
			break;
		}
		case 62: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 79: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 80: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 81: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 82: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(128); break;
		}
	}

	void Factor(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0);
		while (la.kind == 43 || la.kind == 85 || la.kind == 86) {
			MulOp(out x, out op);
			UnaryExpression(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 83) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 84) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(129);
	}

	void UnaryExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		switch (la.kind) {
		case 84: {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = new BinaryExpr(x, BinaryExpr.Opcode.Sub, new LiteralExpr(x, 0), e); 
			break;
		}
		case 87: case 88: {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.Not, e); 
			break;
		}
		case 38: case 54: case 60: case 98: case 99: case 100: case 101: {
			EndlessExpression(out e);
			break;
		}
		case 1: {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 50 || la.kind == 52) {
				Suffix(ref e);
			}
			break;
		}
		case 7: case 50: {
			DisplayExpr(out e);
			break;
		}
		case 2: case 16: case 33: case 89: case 90: case 91: case 92: case 93: case 94: case 95: {
			ConstAtomExpression(out e);
			while (la.kind == 50 || la.kind == 52) {
				Suffix(ref e);
			}
			break;
		}
		default: SynErr(130); break;
		}
	}

	void MulOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 43) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 85) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 86) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(131);
	}

	void NegOp() {
		if (la.kind == 87) {
			Get();
		} else if (la.kind == 88) {
			Get();
		} else SynErr(132);
	}

	void EndlessExpression(out Expression e) {
		IToken/*!*/ x;
		Expression e0, e1;
		e = dummyExpr;
		
		if (la.kind == 54) {
			Get();
			x = t; 
			Expression(out e);
			Expect(96);
			Expression(out e0);
			Expect(55);
			Expression(out e1);
			e = new ITEExpr(x, e, e0, e1); 
		} else if (la.kind == 60) {
			MatchExpression(out e);
		} else if (StartOf(15)) {
			QuantifierGuts(out e);
		} else if (la.kind == 38) {
			ComprehensionExpr(out e);
		} else SynErr(133);
	}

	void DottedIdentifiersAndFunction(out Expression e) {
		IToken id;  IToken openParen = null;
		List<Expression> args = null;
		List<IToken> idents = new List<IToken>();
		
		Ident(out id);
		idents.Add(id); 
		while (la.kind == 52) {
			Get();
			Ident(out id);
			idents.Add(id); 
		}
		if (la.kind == 33) {
			Get();
			openParen = t;  args = new List<Expression>(); 
			if (StartOf(6)) {
				Expressions(args);
			}
			Expect(34);
		}
		e = new IdentifierSequence(idents, openParen, args); 
	}

	void Suffix(ref Expression/*!*/ e) {
		Contract.Requires(e != null); Contract.Ensures(e!=null); IToken/*!*/ id, x;  List<Expression/*!*/>/*!*/ args;
		Expression e0 = null;  Expression e1 = null;  Expression/*!*/ ee;  bool anyDots = false;
		List<Expression> multipleIndices = null;
		bool func = false;
		
		if (la.kind == 52) {
			Get();
			Ident(out id);
			if (la.kind == 33) {
				Get();
				args = new List<Expression/*!*/>();  func = true; 
				if (StartOf(6)) {
					Expressions(args);
				}
				Expect(34);
				e = new FunctionCallExpr(id, id.val, e, args); 
			}
			if (!func) { e = new FieldSelectExpr(id, e, id.val); } 
		} else if (la.kind == 50) {
			Get();
			x = t; 
			if (StartOf(6)) {
				Expression(out ee);
				e0 = ee; 
				if (la.kind == 97) {
					Get();
					anyDots = true; 
					if (StartOf(6)) {
						Expression(out ee);
						e1 = ee; 
					}
				} else if (la.kind == 48) {
					Get();
					Expression(out ee);
					e1 = ee; 
				} else if (la.kind == 19 || la.kind == 51) {
					while (la.kind == 19) {
						Get();
						Expression(out ee);
						if (multipleIndices == null) {
						 multipleIndices = new List<Expression>();
						 multipleIndices.Add(e0);
						}
						multipleIndices.Add(ee);
						
					}
				} else SynErr(134);
			} else if (la.kind == 97) {
				Get();
				Expression(out ee);
				anyDots = true;  e1 = ee; 
			} else SynErr(135);
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
			    Contract.Assert(e0 != null || e1 != null);
			    e = new SeqSelectExpr(x, false, e, e0, e1);
			  } else if (e1 == null) {
			    Contract.Assert(e0 != null);
			    e = new SeqSelectExpr(x, true, e, e0, null);
			  } else {
			    Contract.Assert(e0 != null);
			    e = new SeqUpdateExpr(x, e, e0, e1);
			  }
			}
			
			Expect(51);
		} else SynErr(136);
	}

	void DisplayExpr(out Expression e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  List<Expression/*!*/>/*!*/ elements;
		e = dummyExpr;
		
		if (la.kind == 7) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(6)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements); 
			Expect(8);
		} else if (la.kind == 50) {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(6)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(51);
		} else SynErr(137);
	}

	void ConstAtomExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;
		e = dummyExpr;
		
		switch (la.kind) {
		case 89: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 90: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 91: {
			Get();
			e = new LiteralExpr(t); 
			break;
		}
		case 2: {
			Nat(out n);
			e = new LiteralExpr(t, n); 
			break;
		}
		case 92: {
			Get();
			e = new ThisExpr(t); 
			break;
		}
		case 93: {
			Get();
			x = t; 
			Expect(33);
			Expression(out e);
			Expect(34);
			e = new FreshExpr(x, e); 
			break;
		}
		case 94: {
			Get();
			x = t; 
			Expect(33);
			Expression(out e);
			Expect(34);
			e = new AllocatedExpr(x, e); 
			break;
		}
		case 95: {
			Get();
			x = t; 
			Expect(33);
			Expression(out e);
			Expect(34);
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
		case 33: {
			Get();
			x = t; 
			Expression(out e);
			e = new ParensExpression(x, e); 
			Expect(34);
			break;
		}
		default: SynErr(138); break;
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
		
		Expect(60);
		x = t; 
		Expression(out e);
		while (la.kind == 56) {
			CaseExpression(out c);
			cases.Add(c); 
		}
		e = new MatchExpr(x, e, cases); 
	}

	void QuantifierGuts(out Expression/*!*/ q) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		BoundVar/*!*/ bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar/*!*/>();
		Attributes attrs = null;
		Triggers trigs = null;
		Expression range = null;
		Expression/*!*/ body;
		
		if (la.kind == 98 || la.kind == 99) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 100 || la.kind == 101) {
			Exists();
			x = t; 
		} else SynErr(139);
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 19) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		while (la.kind == 7) {
			AttributeOrTrigger(ref attrs, ref trigs);
		}
		if (la.kind == 16) {
			Get();
			Expression(out range);
		}
		QSep();
		Expression(out body);
		if (univ) {
		 q = new ForallExpr(x, bvars, range, body, trigs, attrs);
		} else {
		  q = new ExistsExpr(x, bvars, range, body, trigs, attrs);
		}
		
	}

	void ComprehensionExpr(out Expression/*!*/ q) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null);
		IToken/*!*/ x = Token.NoToken;
		BoundVar/*!*/ bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar/*!*/>();
		Expression/*!*/ range;
		Expression body = null;
		
		Expect(38);
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
		if (la.kind == 102 || la.kind == 103) {
			QSep();
			Expression(out body);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(x, bvars, range, body);
		
	}

	void CaseExpression(out MatchCaseExpr/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id, arg;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		Expression/*!*/ body;
		
		Expect(56);
		x = t; 
		Ident(out id);
		if (la.kind == 33) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			while (la.kind == 19) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			}
			Expect(34);
		}
		Expect(57);
		Expression(out body);
		c = new MatchCaseExpr(x, id.val, arguments, body); 
	}

	void Forall() {
		if (la.kind == 98) {
			Get();
		} else if (la.kind == 99) {
			Get();
		} else SynErr(140);
	}

	void Exists() {
		if (la.kind == 100) {
			Get();
		} else if (la.kind == 101) {
			Get();
		} else SynErr(141);
	}

	void AttributeOrTrigger(ref Attributes attrs, ref Triggers trigs) {
		List<Expression/*!*/> es = new List<Expression/*!*/>();
		
		Expect(7);
		if (la.kind == 22) {
			AttributeBody(ref attrs);
		} else if (StartOf(6)) {
			es = new List<Expression/*!*/>(); 
			Expressions(es);
			trigs = new Triggers(es, trigs); 
		} else SynErr(142);
		Expect(8);
	}

	void QSep() {
		if (la.kind == 102) {
			Get();
		} else if (la.kind == 103) {
			Get();
		} else SynErr(143);
	}

	void AttributeBody(ref Attributes attrs) {
		string aName;
		List<Attributes.Argument/*!*/> aArgs = new List<Attributes.Argument/*!*/>();
		Attributes.Argument/*!*/ aArg;
		
		Expect(22);
		Expect(1);
		aName = t.val; 
		if (StartOf(16)) {
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
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,T,x,x, x,T,T,T, T,T,T,x, x,x,T,x, T,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,T,x, T,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,x,T, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,x,x, x,x},
		{x,T,T,x, x,x,x,T, x,x,x,T, x,x,x,x, T,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,T,T, x,x,x,x, x,x,T,x, x,x,T,x, T,T,x,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,x,x,T, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,x,x, x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,x,x,T, x,x,x,x, x,T,T,x, x,T,T,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,x,x, x,x},
		{x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x},
		{x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,T,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, T,T,T,T, T,T,T,T, x,x,T,T, T,T,x,x, x,x}

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
	public virtual void SynErr(string filename, int line, int col, string msg) {
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
			case 20: s = "\"replaces\" expected"; break;
			case 21: s = "\"by\" expected"; break;
			case 22: s = "\":\" expected"; break;
			case 23: s = "\"<\" expected"; break;
			case 24: s = "\">\" expected"; break;
			case 25: s = "\"method\" expected"; break;
			case 26: s = "\"constructor\" expected"; break;
			case 27: s = "\"returns\" expected"; break;
			case 28: s = "\"modifies\" expected"; break;
			case 29: s = "\"free\" expected"; break;
			case 30: s = "\"requires\" expected"; break;
			case 31: s = "\"ensures\" expected"; break;
			case 32: s = "\"decreases\" expected"; break;
			case 33: s = "\"(\" expected"; break;
			case 34: s = "\")\" expected"; break;
			case 35: s = "\"bool\" expected"; break;
			case 36: s = "\"nat\" expected"; break;
			case 37: s = "\"int\" expected"; break;
			case 38: s = "\"set\" expected"; break;
			case 39: s = "\"seq\" expected"; break;
			case 40: s = "\"object\" expected"; break;
			case 41: s = "\"function\" expected"; break;
			case 42: s = "\"reads\" expected"; break;
			case 43: s = "\"*\" expected"; break;
			case 44: s = "\"`\" expected"; break;
			case 45: s = "\"label\" expected"; break;
			case 46: s = "\"break\" expected"; break;
			case 47: s = "\"return\" expected"; break;
			case 48: s = "\":=\" expected"; break;
			case 49: s = "\"new\" expected"; break;
			case 50: s = "\"[\" expected"; break;
			case 51: s = "\"]\" expected"; break;
			case 52: s = "\".\" expected"; break;
			case 53: s = "\"choose\" expected"; break;
			case 54: s = "\"if\" expected"; break;
			case 55: s = "\"else\" expected"; break;
			case 56: s = "\"case\" expected"; break;
			case 57: s = "\"=>\" expected"; break;
			case 58: s = "\"while\" expected"; break;
			case 59: s = "\"invariant\" expected"; break;
			case 60: s = "\"match\" expected"; break;
			case 61: s = "\"foreach\" expected"; break;
			case 62: s = "\"in\" expected"; break;
			case 63: s = "\"assert\" expected"; break;
			case 64: s = "\"assume\" expected"; break;
			case 65: s = "\"print\" expected"; break;
			case 66: s = "\"<==>\" expected"; break;
			case 67: s = "\"\\u21d4\" expected"; break;
			case 68: s = "\"==>\" expected"; break;
			case 69: s = "\"\\u21d2\" expected"; break;
			case 70: s = "\"&&\" expected"; break;
			case 71: s = "\"\\u2227\" expected"; break;
			case 72: s = "\"||\" expected"; break;
			case 73: s = "\"\\u2228\" expected"; break;
			case 74: s = "\"==\" expected"; break;
			case 75: s = "\"<=\" expected"; break;
			case 76: s = "\">=\" expected"; break;
			case 77: s = "\"!=\" expected"; break;
			case 78: s = "\"!!\" expected"; break;
			case 79: s = "\"!in\" expected"; break;
			case 80: s = "\"\\u2260\" expected"; break;
			case 81: s = "\"\\u2264\" expected"; break;
			case 82: s = "\"\\u2265\" expected"; break;
			case 83: s = "\"+\" expected"; break;
			case 84: s = "\"-\" expected"; break;
			case 85: s = "\"/\" expected"; break;
			case 86: s = "\"%\" expected"; break;
			case 87: s = "\"!\" expected"; break;
			case 88: s = "\"\\u00ac\" expected"; break;
			case 89: s = "\"false\" expected"; break;
			case 90: s = "\"true\" expected"; break;
			case 91: s = "\"null\" expected"; break;
			case 92: s = "\"this\" expected"; break;
			case 93: s = "\"fresh\" expected"; break;
			case 94: s = "\"allocated\" expected"; break;
			case 95: s = "\"old\" expected"; break;
			case 96: s = "\"then\" expected"; break;
			case 97: s = "\"..\" expected"; break;
			case 98: s = "\"forall\" expected"; break;
			case 99: s = "\"\\u2200\" expected"; break;
			case 100: s = "\"exists\" expected"; break;
			case 101: s = "\"\\u2203\" expected"; break;
			case 102: s = "\"::\" expected"; break;
			case 103: s = "\"\\u2022\" expected"; break;
			case 104: s = "??? expected"; break;
			case 105: s = "invalid ClassMemberDecl"; break;
			case 106: s = "invalid MethodDecl"; break;
			case 107: s = "invalid TypeAndToken"; break;
			case 108: s = "invalid MethodSpec"; break;
			case 109: s = "invalid MethodSpec"; break;
			case 110: s = "invalid ReferenceType"; break;
			case 111: s = "invalid FunctionSpec"; break;
			case 112: s = "invalid PossiblyWildFrameExpression"; break;
			case 113: s = "invalid PossiblyWildExpression"; break;
			case 114: s = "invalid OneStmt"; break;
			case 115: s = "invalid OneStmt"; break;
			case 116: s = "invalid UpdateStmt"; break;
			case 117: s = "invalid IfStmt"; break;
			case 118: s = "invalid IfStmt"; break;
			case 119: s = "invalid WhileStmt"; break;
			case 120: s = "invalid Rhs"; break;
			case 121: s = "invalid Lhs"; break;
			case 122: s = "invalid Guard"; break;
			case 123: s = "invalid AttributeArg"; break;
			case 124: s = "invalid EquivOp"; break;
			case 125: s = "invalid ImpliesOp"; break;
			case 126: s = "invalid AndOp"; break;
			case 127: s = "invalid OrOp"; break;
			case 128: s = "invalid RelOp"; break;
			case 129: s = "invalid AddOp"; break;
			case 130: s = "invalid UnaryExpression"; break;
			case 131: s = "invalid MulOp"; break;
			case 132: s = "invalid NegOp"; break;
			case 133: s = "invalid EndlessExpression"; break;
			case 134: s = "invalid Suffix"; break;
			case 135: s = "invalid Suffix"; break;
			case 136: s = "invalid Suffix"; break;
			case 137: s = "invalid DisplayExpr"; break;
			case 138: s = "invalid ConstAtomExpression"; break;
			case 139: s = "invalid QuantifierGuts"; break;
			case 140: s = "invalid Forall"; break;
			case 141: s = "invalid Exists"; break;
			case 142: s = "invalid AttributeOrTrigger"; break;
			case 143: s = "invalid QSep"; break;

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