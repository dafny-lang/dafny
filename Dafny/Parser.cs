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
static Statement/*!*/ dummyStmt = new ReturnStmt(Token.NoToken);
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
				ClassMemberDecl(membersDefaultClass);
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
			ClassMemberDecl(members);
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
		if (la.kind == 7) {
			Get();
			bodyStart = t; 
			while (la.kind == 1 || la.kind == 7) {
				DatatypeMemberDecl(ctors);
				Expect(15);
			}
			Expect(8);
		} else if (la.kind == 16) {
			Get();
			bodyStart = t; 
			DatatypeMemberDecl(ctors);
			while (la.kind == 17) {
				Get();
				DatatypeMemberDecl(ctors);
			}
			Expect(15);
		} else SynErr(106);
		dt = new DatatypeDecl(id, id.val, module, typeArgs, ctors, attrs);
		dt.BodyStartTok = bodyStart;
		dt.BodyEndTok = t;
		
	}

	void ClassMemberDecl(List<MemberDecl/*!*/>/*!*/ mm) {
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
		} else if (la.kind == 40) {
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (la.kind == 10 || la.kind == 25) {
			MethodDecl(mmod, out m);
			mm.Add(m); 
		} else if (la.kind == 20) {
			CouplingInvDecl(mmod, mm);
		} else SynErr(107);
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
		Expect(15);
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
		
		Expect(40);
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
		if (la.kind == 15) {
			Get();
			while (StartOf(3)) {
				FunctionSpec(reqs, reads, ens, decreases);
			}
		} else if (StartOf(4)) {
			while (StartOf(3)) {
				FunctionSpec(reqs, reads, ens, decreases);
			}
			FunctionBody(out bb, out bodyStart, out bodyEnd);
			body = bb; 
		} else SynErr(108);
		f = new Function(id, id.val, mmod.IsStatic, !isFunctionMethod, mmod.IsUnlimited, typeArgs, formals, returnType, reqs, reads, ens, decreases, body, attrs);
		f.BodyStartTok = bodyStart;
		f.BodyEndTok = bodyEnd;
		
	}

	void MethodDecl(MemberModifiers mmod, out Method/*!*/ m) {
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
		bool isRefinement = false;
		IToken bodyStart = Token.NoToken;
		IToken bodyEnd = Token.NoToken;
		
		if (la.kind == 25) {
			Get();
		} else if (la.kind == 10) {
			Get();
			isRefinement = true; 
		} else SynErr(109);
		if (mmod.IsUnlimited) { SemErr(t, "methods cannot be declared 'unlimited'"); }
		
		while (la.kind == 7) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 23) {
			GenericParameters(typeArgs);
		}
		Formals(true, !mmod.IsGhost, ins);
		if (la.kind == 26) {
			Get();
			Formals(false, true, outs);
		}
		if (la.kind == 15) {
			Get();
			while (StartOf(5)) {
				MethodSpec(req, mod, ens, dec);
			}
		} else if (StartOf(6)) {
			while (StartOf(5)) {
				MethodSpec(req, mod, ens, dec);
			}
			BlockStmt(out bb, out bodyStart, out bodyEnd);
			body = (BlockStmt)bb; 
		} else SynErr(110);
		if (isRefinement)
		 m = new MethodRefinement(id, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs, req, mod, ens, dec, body, attrs);
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
		Expect(15);
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
		if (la.kind == 32) {
			FormalsOptionalIds(formals);
		}
		ctors.Add(new DatatypeCtor(id, id.val, formals, attrs)); 
	}

	void FormalsOptionalIds(List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  string/*!*/ name;  bool isGhost; 
		Expect(32);
		if (StartOf(7)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost)); 
			while (la.kind == 19) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost)); 
			}
		}
		Expect(33);
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

	void GIdentType(bool allowGhost, out IToken/*!*/ id, out Type/*!*/ ty, out bool isGhost) {
		Contract.Ensures(Contract.ValueAtReturn(out id)!=null);
		Contract.Ensures(Contract.ValueAtReturn(out ty)!=null);
		isGhost = false; 
		if (la.kind == 11) {
			Get();
			if (allowGhost) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
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
		case 34: {
			Get();
			tok = t; 
			break;
		}
		case 35: {
			Get();
			tok = t;  ty = new NatType(); 
			break;
		}
		case 36: {
			Get();
			tok = t;  ty = new IntType(); 
			break;
		}
		case 37: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("set type expects exactly one type argument");
			}
			ty = new SetType(gt[0]);
			
			break;
		}
		case 38: {
			Get();
			tok = t;  gt = new List<Type/*!*/>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("seq type expects exactly one type argument");
			}
			ty = new SeqType(gt[0]);
			
			break;
		}
		case 1: case 3: case 39: {
			ReferenceType(out tok, out ty);
			break;
		}
		default: SynErr(111); break;
		}
	}

	void Formals(bool incoming, bool allowGhosts, List<Formal/*!*/>/*!*/ formals) {
		Contract.Requires(cce.NonNullElements(formals)); IToken/*!*/ id;  Type/*!*/ ty;  bool isGhost; 
		Expect(32);
		if (la.kind == 1 || la.kind == 11) {
			GIdentType(allowGhosts, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			while (la.kind == 19) {
				Get();
				GIdentType(allowGhosts, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost)); 
			}
		}
		Expect(33);
	}

	void MethodSpec(List<MaybeFreeExpression/*!*/>/*!*/ req, List<FrameExpression/*!*/>/*!*/ mod, List<MaybeFreeExpression/*!*/>/*!*/ ens,
List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(req)); Contract.Requires(cce.NonNullElements(mod)); Contract.Requires(cce.NonNullElements(ens)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe;  bool isFree = false;
		
		if (la.kind == 27) {
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
			Expect(15);
		} else if (la.kind == 28 || la.kind == 29 || la.kind == 30) {
			if (la.kind == 28) {
				Get();
				isFree = true; 
			}
			if (la.kind == 29) {
				Get();
				Expression(out e);
				Expect(15);
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 30) {
				Get();
				Expression(out e);
				Expect(15);
				ens.Add(new MaybeFreeExpression(e, isFree)); 
			} else SynErr(112);
		} else if (la.kind == 31) {
			Get();
			Expressions(decreases);
			Expect(15);
		} else SynErr(113);
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
		if (la.kind == 43) {
			Get();
			Ident(out id);
			fieldName = id.val; 
		}
		fe = new FrameExpression(e, fieldName); 
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
		
		if (la.kind == 39) {
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
		} else SynErr(114);
	}

	void FunctionSpec(List<Expression/*!*/>/*!*/ reqs, List<FrameExpression/*!*/>/*!*/ reads, List<Expression/*!*/>/*!*/ ens, List<Expression/*!*/>/*!*/ decreases) {
		Contract.Requires(cce.NonNullElements(reqs)); Contract.Requires(cce.NonNullElements(reads)); Contract.Requires(cce.NonNullElements(decreases));
		Expression/*!*/ e;  FrameExpression/*!*/ fe; 
		if (la.kind == 29) {
			Get();
			Expression(out e);
			Expect(15);
			reqs.Add(e); 
		} else if (la.kind == 41) {
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
			Expect(15);
		} else if (la.kind == 30) {
			Get();
			Expression(out e);
			Expect(15);
			ens.Add(e); 
		} else if (la.kind == 31) {
			Get();
			Expressions(decreases);
			Expect(15);
		} else SynErr(115);
	}

	void FunctionBody(out Expression/*!*/ e, out IToken bodyStart, out IToken bodyEnd) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); e = dummyExpr; 
		Expect(7);
		bodyStart = t; 
		if (la.kind == 44) {
			MatchExpression(out e);
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(116);
		Expect(8);
		bodyEnd = t; 
	}

	void PossiblyWildFrameExpression(out FrameExpression/*!*/ fe) {
		Contract.Ensures(Contract.ValueAtReturn(out fe) != null); fe = dummyFrameExpr; 
		if (la.kind == 42) {
			Get();
			fe = new FrameExpression(new WildcardExpr(t), null); 
		} else if (StartOf(8)) {
			FrameExpression(out fe);
		} else SynErr(117);
	}

	void PossiblyWildExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e)!=null);
		e = dummyExpr; 
		if (la.kind == 42) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(118);
	}

	void MatchExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  MatchCaseExpr/*!*/ c;
		List<MatchCaseExpr/*!*/> cases = new List<MatchCaseExpr/*!*/>();
		
		Expect(44);
		x = t; 
		Expression(out e);
		while (la.kind == 45) {
			CaseExpression(out c);
			cases.Add(c); 
		}
		e = new MatchExpr(x, e, cases); 
	}

	void CaseExpression(out MatchCaseExpr/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null); IToken/*!*/ x, id, arg;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		Expression/*!*/ body;
		
		Expect(45);
		x = t; 
		Ident(out id);
		if (la.kind == 32) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			while (la.kind == 19) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			}
			Expect(33);
		}
		Expect(46);
		MatchOrExpr(out body);
		c = new MatchCaseExpr(x, id.val, arguments, body); 
	}

	void MatchOrExpr(out Expression/*!*/ e) {
		e = dummyExpr; 
		if (la.kind == 32) {
			Get();
			MatchOrExpr(out e);
			Expect(33);
		} else if (la.kind == 44) {
			MatchExpression(out e);
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(119);
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
		
		if (la.kind == 7) {
			BlockStmt(out s, out bodyStart, out bodyEnd);
		} else if (la.kind == 63) {
			AssertStmt(out s);
		} else if (la.kind == 64) {
			AssumeStmt(out s);
		} else if (la.kind == 65) {
			UseStmt(out s);
		} else if (la.kind == 66) {
			PrintStmt(out s);
		} else if (StartOf(11)) {
			UpdateStmt(out s);
		} else if (la.kind == 56) {
			HavocStmt(out s);
		} else if (la.kind == 11 || la.kind == 18) {
			VarDeclStatement(out s);
		} else if (la.kind == 57) {
			IfStmt(out s);
		} else if (la.kind == 59) {
			WhileStmt(out s);
		} else if (la.kind == 44) {
			MatchStmt(out s);
		} else if (la.kind == 61) {
			ForeachStmt(out s);
		} else if (la.kind == 47) {
			Get();
			x = t; 
			Ident(out id);
			Expect(22);
			OneStmt(out s);
			s.Labels = new LabelNode(x, id.val, s.Labels); 
		} else if (la.kind == 48) {
			Get();
			x = t; breakCount = 1; label = null; 
			if (la.kind == 1) {
				Ident(out id);
				label = id.val; 
			} else if (la.kind == 15 || la.kind == 48) {
				while (la.kind == 48) {
					Get();
					breakCount++; 
				}
			} else SynErr(120);
			Expect(15);
			s = label != null ? new BreakStmt(x, label) : new BreakStmt(x, breakCount); 
		} else if (la.kind == 49) {
			Get();
			x = t; 
			Expect(15);
			s = new ReturnStmt(x); 
		} else SynErr(121);
	}

	void AssertStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ e; 
		Expect(63);
		x = t; 
		Expression(out e);
		Expect(15);
		s = new AssertStmt(x, e); 
	}

	void AssumeStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ e; 
		Expect(64);
		x = t; 
		Expression(out e);
		Expect(15);
		s = new AssumeStmt(x, e); 
	}

	void UseStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ e; 
		Expect(65);
		x = t; 
		Expression(out e);
		Expect(15);
		s = new UseStmt(x, e); 
	}

	void PrintStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Attributes.Argument/*!*/ arg;
		List<Attributes.Argument/*!*/> args = new List<Attributes.Argument/*!*/>();
		
		Expect(66);
		x = t; 
		AttributeArg(out arg);
		args.Add(arg); 
		while (la.kind == 19) {
			Get();
			AttributeArg(out arg);
			args.Add(arg); 
		}
		Expect(15);
		s = new PrintStmt(x, args); 
	}

	void UpdateStmt(out Statement/*!*/ s) {
		List<Expression> lhss = new List<Expression>();
		List<DeterminedAssignmentRhs> rhss = new List<DeterminedAssignmentRhs>();
		Expression e;  DeterminedAssignmentRhs r;
		Expression lhs0;
		IToken x;
		
		Lhs(out e);
		x = e.tok; 
		if (la.kind == 15) {
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
			Expect(15);
		} else if (la.kind == 22) {
			Get();
			SemErr(t, "invalid statement (did you forget the 'label' keyword?)"); 
		} else SynErr(122);
		s = new UpdateStmt(x, lhss, rhss); 
	}

	void HavocStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null); IToken/*!*/ x;  Expression/*!*/ lhs; 
		Expect(56);
		x = t; 
		Lhs(out lhs);
		Expect(15);
		s = new AssignStmt(x, lhs); 
	}

	void VarDeclStatement(out Statement/*!*/ s) {
		IToken x = null, assignTok = null;  bool isGhost = false;
		VarDecl/*!*/ d;
		DeterminedAssignmentRhs r;  Expression lhs0;
		List<VarDecl> lhss = new List<VarDecl>();
		List<DeterminedAssignmentRhs> rhss = new List<DeterminedAssignmentRhs>();
		
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
			assignTok = t;  lhs0 = new IdentifierExpr(lhss[0].Tok, lhss[0].Name); 
			Rhs(out r, lhs0);
			rhss.Add(r); 
			while (la.kind == 19) {
				Get();
				Rhs(out r, lhs0);
				rhss.Add(r); 
			}
		}
		Expect(15);
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
		
		Expect(57);
		x = t; 
		if (la.kind == 32) {
			Guard(out guard);
			BlockStmt(out thn, out bodyStart, out bodyEnd);
			if (la.kind == 58) {
				Get();
				if (la.kind == 57) {
					IfStmt(out s);
					els = s; 
				} else if (la.kind == 7) {
					BlockStmt(out s, out bodyStart, out bodyEnd);
					els = s; 
				} else SynErr(123);
			}
			ifStmt = new IfStmt(x, guard, thn, els); 
		} else if (la.kind == 7) {
			AlternativeBlock(out alternatives);
			ifStmt = new AlternativeStmt(x, alternatives); 
		} else SynErr(124);
	}

	void WhileStmt(out Statement/*!*/ stmt) {
		Contract.Ensures(Contract.ValueAtReturn(out stmt) != null); IToken/*!*/ x;
		Expression guard;
		List<MaybeFreeExpression/*!*/> invariants = new List<MaybeFreeExpression/*!*/>();
		List<Expression/*!*/> decreases = new List<Expression/*!*/>();
		Statement/*!*/ body;
		IToken bodyStart, bodyEnd;
		List<GuardedAlternative> alternatives;
		stmt = dummyStmt;  // to please the compiler
		
		Expect(59);
		x = t; 
		if (la.kind == 32) {
			Guard(out guard);
			Contract.Assume(guard == null || cce.Owner.None(guard)); 
			LoopSpec(out invariants, out decreases);
			BlockStmt(out body, out bodyStart, out bodyEnd);
			stmt = new WhileStmt(x, guard, invariants, decreases, body); 
		} else if (StartOf(12)) {
			LoopSpec(out invariants, out decreases);
			AlternativeBlock(out alternatives);
			stmt = new AlternativeLoopStmt(x, invariants, decreases, alternatives); 
		} else SynErr(125);
	}

	void MatchStmt(out Statement/*!*/ s) {
		Contract.Ensures(Contract.ValueAtReturn(out s) != null);
		Token x;  Expression/*!*/ e;  MatchCaseStmt/*!*/ c;
		List<MatchCaseStmt/*!*/> cases = new List<MatchCaseStmt/*!*/>(); 
		Expect(44);
		x = t; 
		Expression(out e);
		Expect(7);
		while (la.kind == 45) {
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
		
		Expect(32);
		Ident(out boundVar);
		if (la.kind == 22) {
			Get();
			Type(out ty);
		}
		Expect(62);
		Expression(out collection);
		if (la.kind == 17) {
			Get();
			Expression(out range);
		}
		Expect(33);
		Expect(7);
		while (la.kind == 63 || la.kind == 64 || la.kind == 65) {
			if (la.kind == 63) {
				AssertStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			} else if (la.kind == 64) {
				AssumeStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			} else {
				UseStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			}
		}
		if (StartOf(11)) {
			UpdateStmt(out s);
			bodyAssign = s; 
		} else if (la.kind == 56) {
			HavocStmt(out s);
			bodyAssign = s; 
		} else SynErr(126);
		Expect(8);
		if (bodyAssign != null) {
		 s = new ForeachStmt(x, new BoundVar(boundVar, boundVar.val, ty), collection, range, bodyPrefix, bodyAssign);
		} else {
		  s = dummyStmt;  // some error occurred in parsing the bodyAssign
		}
		
	}

	void Lhs(out Expression e) {
		e = null;  // to please the compiler
		
		if (la.kind == 1) {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else if (StartOf(13)) {
			ConstAtomExpression(out e);
			Suffix(ref e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else SynErr(127);
	}

	void Rhs(out DeterminedAssignmentRhs r, Expression receiverForInitCall) {
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
					Expect(32);
					args = new List<Expression/*!*/>(); 
					if (StartOf(8)) {
						Expressions(args);
					}
					Expect(33);
					initCall = new CallStmt(x, new List<IdentifierExpr>(),
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
		} else if (StartOf(8)) {
			Expression(out e);
			r = new ExprRhs(e); 
		} else SynErr(128);
	}

	void Guard(out Expression e) {
		Expression/*!*/ ee;  e = null; 
		Expect(32);
		if (la.kind == 42) {
			Get();
			e = null; 
		} else if (StartOf(8)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(129);
		Expect(33);
	}

	void AlternativeBlock(out List<GuardedAlternative> alternatives) {
		alternatives = new List<GuardedAlternative>();
		IToken x;
		Expression e;
		List<Statement> body;
		
		Expect(7);
		while (la.kind == 45) {
			Get();
			x = t; 
			Expression(out e);
			Expect(46);
			body = new List<Statement>(); 
			while (StartOf(9)) {
				Stmt(body);
			}
			alternatives.Add(new GuardedAlternative(x, e, body)); 
		}
		Expect(8);
	}

	void LoopSpec(out List<MaybeFreeExpression/*!*/> invariants, out List<Expression/*!*/> decreases) {
		bool isFree;  Expression/*!*/ e;
		invariants = new List<MaybeFreeExpression/*!*/>();
		decreases = new List<Expression/*!*/>();
		
		while (la.kind == 28 || la.kind == 31 || la.kind == 60) {
			if (la.kind == 28 || la.kind == 60) {
				isFree = false; 
				if (la.kind == 28) {
					Get();
					isFree = true; 
				}
				Expect(60);
				Expression(out e);
				invariants.Add(new MaybeFreeExpression(e, isFree)); 
				Expect(15);
			} else {
				Get();
				PossiblyWildExpression(out e);
				decreases.Add(e); 
				while (la.kind == 19) {
					Get();
					PossiblyWildExpression(out e);
					decreases.Add(e); 
				}
				Expect(15);
			}
		}
	}

	void CaseStatement(out MatchCaseStmt/*!*/ c) {
		Contract.Ensures(Contract.ValueAtReturn(out c) != null);
		IToken/*!*/ x, id, arg;
		List<BoundVar/*!*/> arguments = new List<BoundVar/*!*/>();
		List<Statement/*!*/> body = new List<Statement/*!*/>();
		
		Expect(45);
		x = t; 
		Ident(out id);
		if (la.kind == 32) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			while (la.kind == 19) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy())); 
			}
			Expect(33);
		}
		Expect(46);
		while (StartOf(9)) {
			Stmt(body);
		}
		c = new MatchCaseStmt(x, id.val, arguments, body); 
	}

	void AttributeArg(out Attributes.Argument/*!*/ arg) {
		Contract.Ensures(Contract.ValueAtReturn(out arg) != null); Expression/*!*/ e;  arg = dummyAttrArg; 
		if (la.kind == 4) {
			Get();
			arg = new Attributes.Argument(t.val.Substring(1, t.val.Length-2)); 
		} else if (StartOf(8)) {
			Expression(out e);
			arg = new Attributes.Argument(e); 
		} else SynErr(130);
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
		} else SynErr(131);
	}

	void LogicalExpression(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1; 
		RelationalExpression(out e0);
		if (StartOf(14)) {
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
		} else SynErr(132);
	}

	void RelationalExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken x, firstOpTok = null;  Expression e0, e1;  BinaryExpr.Opcode op;
		List<Expression> chain = null;
		List<BinaryExpr.Opcode> ops = null;
		int kind = 0;  // 0 ("uncommitted") indicates chain of ==, possibly with one !=
		               // 1 ("ascending")   indicates chain of ==, <, <=, possibly with one !=
		               // 2 ("descending")  indicates chain of ==, >, >=, possibly with one !=
		               // 3 ("illegal")     indicates illegal chain
		bool hasSeenNeq = false;
		
		Term(out e0);
		e = e0; 
		if (StartOf(15)) {
			RelOp(out x, out op);
			firstOpTok = x; 
			Term(out e1);
			e = new BinaryExpr(x, op, e0, e1); 
			while (StartOf(15)) {
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
				   default:
				     kind = 3;  break;
				 }
				}
				e0 = e1;
				
				RelOp(out x, out op);
				switch (op) {
				 case BinaryExpr.Opcode.Eq:
				   if (kind == 3) { SemErr(x, "chaining not allowed from the previous operator"); }
				   break;
				 case BinaryExpr.Opcode.Neq:
				   if (hasSeenNeq) { SemErr(x, "a chain cannot have more than one != operator"); }
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
				 default:
				   SemErr(x, "this operator cannot be part of a chain");
				   kind = 3;  break;
				}
				
				Term(out e1);
				ops.Add(op); chain.Add(e1);
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
		} else SynErr(133);
	}

	void OrOp() {
		if (la.kind == 73) {
			Get();
		} else if (la.kind == 74) {
			Get();
		} else SynErr(134);
	}

	void Term(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		Factor(out e0);
		while (la.kind == 84 || la.kind == 85) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void RelOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		switch (la.kind) {
		case 75: {
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
		case 62: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 80: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 81: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 82: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 83: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(135); break;
		}
	}

	void Factor(out Expression/*!*/ e0) {
		Contract.Ensures(Contract.ValueAtReturn(out e0) != null); IToken/*!*/ x;  Expression/*!*/ e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0);
		while (la.kind == 42 || la.kind == 86 || la.kind == 87) {
			MulOp(out x, out op);
			UnaryExpression(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 84) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 85) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(136);
	}

	void UnaryExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null); IToken/*!*/ x;  e = dummyExpr; 
		if (la.kind == 85) {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = new BinaryExpr(x, BinaryExpr.Opcode.Sub, new LiteralExpr(x, 0), e); 
		} else if (la.kind == 88 || la.kind == 89) {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.Not, e); 
		} else if (StartOf(16)) {
			EndlessExpression(out e);
		} else if (la.kind == 1) {
			DottedIdentifiersAndFunction(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else if (StartOf(13)) {
			ConstAtomExpression(out e);
			while (la.kind == 52 || la.kind == 54) {
				Suffix(ref e);
			}
		} else SynErr(137);
	}

	void MulOp(out IToken/*!*/ x, out BinaryExpr.Opcode op) {
		Contract.Ensures(Contract.ValueAtReturn(out x) != null); x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 42) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 86) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 87) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(138);
	}

	void NegOp() {
		if (la.kind == 88) {
			Get();
		} else if (la.kind == 89) {
			Get();
		} else SynErr(139);
	}

	void EndlessExpression(out Expression e) {
		IToken/*!*/ x;
		Expression e0, e1;
		e = dummyExpr;
		
		if (la.kind == 57) {
			Get();
			x = t; 
			Expression(out e);
			Expect(97);
			Expression(out e0);
			Expect(58);
			Expression(out e1);
			e = new ITEExpr(x, e, e0, e1); 
		} else if (StartOf(17)) {
			QuantifierGuts(out e);
		} else if (la.kind == 37) {
			ComprehensionExpr(out e);
		} else SynErr(140);
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
		if (la.kind == 32) {
			Get();
			openParen = t;  args = new List<Expression>(); 
			if (StartOf(8)) {
				Expressions(args);
			}
			Expect(33);
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
			if (la.kind == 32) {
				Get();
				args = new List<Expression/*!*/>();  func = true; 
				if (StartOf(8)) {
					Expressions(args);
				}
				Expect(33);
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
				} else SynErr(141);
			} else if (la.kind == 98) {
				Get();
				Expression(out ee);
				anyDots = true;  e1 = ee; 
			} else SynErr(142);
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
			
			Expect(53);
		} else SynErr(143);
	}

	void ConstAtomExpression(out Expression/*!*/ e) {
		Contract.Ensures(Contract.ValueAtReturn(out e) != null);
		IToken/*!*/ x;  BigInteger n;  List<Expression/*!*/>/*!*/ elements;
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
			Expect(32);
			Expression(out e);
			Expect(33);
			e = new FreshExpr(x, e); 
			break;
		}
		case 95: {
			Get();
			x = t; 
			Expect(32);
			Expression(out e);
			Expect(33);
			e = new AllocatedExpr(x, e); 
			break;
		}
		case 96: {
			Get();
			x = t; 
			Expect(32);
			Expression(out e);
			Expect(33);
			e = new OldExpr(x, e); 
			break;
		}
		case 17: {
			Get();
			x = t; 
			Expression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.SeqLength, e); 
			Expect(17);
			break;
		}
		case 7: {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements); 
			Expect(8);
			break;
		}
		case 52: {
			Get();
			x = t;  elements = new List<Expression/*!*/>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(53);
			break;
		}
		case 32: {
			Get();
			x = t; 
			Expression(out e);
			e = new ParensExpression(x, e); 
			Expect(33);
			break;
		}
		default: SynErr(144); break;
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

	void QuantifierGuts(out Expression/*!*/ q) {
		Contract.Ensures(Contract.ValueAtReturn(out q) != null); IToken/*!*/ x = Token.NoToken;
		bool univ = false;
		BoundVar/*!*/ bv;
		List<BoundVar/*!*/> bvars = new List<BoundVar/*!*/>();
		Attributes attrs = null;
		Triggers trigs = null;
		Expression range = null;
		Expression/*!*/ body;
		
		if (la.kind == 99 || la.kind == 100) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 101 || la.kind == 102) {
			Exists();
			x = t; 
		} else SynErr(145);
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
		if (la.kind == 17) {
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
		
		Expect(37);
		x = t; 
		IdentTypeOptional(out bv);
		bvars.Add(bv); 
		while (la.kind == 19) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv); 
		}
		Expect(17);
		Expression(out range);
		if (la.kind == 103 || la.kind == 104) {
			QSep();
			Expression(out body);
		}
		if (body == null && bvars.Count != 1) { SemErr(t, "a set comprehension with more than one bound variable must have a term expression"); }
		q = new SetComprehension(x, bvars, range, body);
		
	}

	void Forall() {
		if (la.kind == 99) {
			Get();
		} else if (la.kind == 100) {
			Get();
		} else SynErr(146);
	}

	void Exists() {
		if (la.kind == 101) {
			Get();
		} else if (la.kind == 102) {
			Get();
		} else SynErr(147);
	}

	void AttributeOrTrigger(ref Attributes attrs, ref Triggers trigs) {
		List<Expression/*!*/> es = new List<Expression/*!*/>();
		
		Expect(7);
		if (la.kind == 22) {
			AttributeBody(ref attrs);
		} else if (StartOf(8)) {
			es = new List<Expression/*!*/>(); 
			Expressions(es);
			trigs = new Triggers(es, trigs); 
		} else SynErr(148);
		Expect(8);
	}

	void QSep() {
		if (la.kind == 103) {
			Get();
		} else if (la.kind == 104) {
			Get();
		} else SynErr(149);
	}

	void AttributeBody(ref Attributes attrs) {
		string aName;
		List<Attributes.Argument/*!*/> aArgs = new List<Attributes.Argument/*!*/>();
		Attributes.Argument/*!*/ aArg;
		
		Expect(22);
		Expect(1);
		aName = t.val; 
		if (StartOf(18)) {
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
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,T,x,x, x,T,T,T, T,T,T,x, x,x,T,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,T,T, T,T,x,x, x,x,T,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,x,T, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,T, x,x,x,x, x,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, T,T,x,x, T,x,x,x, T,T,x,T, x,T,x,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,T,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x},
		{x,T,T,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,T,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,x, x,x,x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,x, x,x,x},
		{x,T,T,x, T,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,T, T,T,T,T, T,x,x,T, T,T,T,x, x,x,x}

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
			case 15: s = "\";\" expected"; break;
			case 16: s = "\"=\" expected"; break;
			case 17: s = "\"|\" expected"; break;
			case 18: s = "\"var\" expected"; break;
			case 19: s = "\",\" expected"; break;
			case 20: s = "\"replaces\" expected"; break;
			case 21: s = "\"by\" expected"; break;
			case 22: s = "\":\" expected"; break;
			case 23: s = "\"<\" expected"; break;
			case 24: s = "\">\" expected"; break;
			case 25: s = "\"method\" expected"; break;
			case 26: s = "\"returns\" expected"; break;
			case 27: s = "\"modifies\" expected"; break;
			case 28: s = "\"free\" expected"; break;
			case 29: s = "\"requires\" expected"; break;
			case 30: s = "\"ensures\" expected"; break;
			case 31: s = "\"decreases\" expected"; break;
			case 32: s = "\"(\" expected"; break;
			case 33: s = "\")\" expected"; break;
			case 34: s = "\"bool\" expected"; break;
			case 35: s = "\"nat\" expected"; break;
			case 36: s = "\"int\" expected"; break;
			case 37: s = "\"set\" expected"; break;
			case 38: s = "\"seq\" expected"; break;
			case 39: s = "\"object\" expected"; break;
			case 40: s = "\"function\" expected"; break;
			case 41: s = "\"reads\" expected"; break;
			case 42: s = "\"*\" expected"; break;
			case 43: s = "\"`\" expected"; break;
			case 44: s = "\"match\" expected"; break;
			case 45: s = "\"case\" expected"; break;
			case 46: s = "\"=>\" expected"; break;
			case 47: s = "\"label\" expected"; break;
			case 48: s = "\"break\" expected"; break;
			case 49: s = "\"return\" expected"; break;
			case 50: s = "\":=\" expected"; break;
			case 51: s = "\"new\" expected"; break;
			case 52: s = "\"[\" expected"; break;
			case 53: s = "\"]\" expected"; break;
			case 54: s = "\".\" expected"; break;
			case 55: s = "\"choose\" expected"; break;
			case 56: s = "\"havoc\" expected"; break;
			case 57: s = "\"if\" expected"; break;
			case 58: s = "\"else\" expected"; break;
			case 59: s = "\"while\" expected"; break;
			case 60: s = "\"invariant\" expected"; break;
			case 61: s = "\"foreach\" expected"; break;
			case 62: s = "\"in\" expected"; break;
			case 63: s = "\"assert\" expected"; break;
			case 64: s = "\"assume\" expected"; break;
			case 65: s = "\"use\" expected"; break;
			case 66: s = "\"print\" expected"; break;
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
			case 80: s = "\"!in\" expected"; break;
			case 81: s = "\"\\u2260\" expected"; break;
			case 82: s = "\"\\u2264\" expected"; break;
			case 83: s = "\"\\u2265\" expected"; break;
			case 84: s = "\"+\" expected"; break;
			case 85: s = "\"-\" expected"; break;
			case 86: s = "\"/\" expected"; break;
			case 87: s = "\"%\" expected"; break;
			case 88: s = "\"!\" expected"; break;
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
			case 106: s = "invalid DatatypeDecl"; break;
			case 107: s = "invalid ClassMemberDecl"; break;
			case 108: s = "invalid FunctionDecl"; break;
			case 109: s = "invalid MethodDecl"; break;
			case 110: s = "invalid MethodDecl"; break;
			case 111: s = "invalid TypeAndToken"; break;
			case 112: s = "invalid MethodSpec"; break;
			case 113: s = "invalid MethodSpec"; break;
			case 114: s = "invalid ReferenceType"; break;
			case 115: s = "invalid FunctionSpec"; break;
			case 116: s = "invalid FunctionBody"; break;
			case 117: s = "invalid PossiblyWildFrameExpression"; break;
			case 118: s = "invalid PossiblyWildExpression"; break;
			case 119: s = "invalid MatchOrExpr"; break;
			case 120: s = "invalid OneStmt"; break;
			case 121: s = "invalid OneStmt"; break;
			case 122: s = "invalid UpdateStmt"; break;
			case 123: s = "invalid IfStmt"; break;
			case 124: s = "invalid IfStmt"; break;
			case 125: s = "invalid WhileStmt"; break;
			case 126: s = "invalid ForeachStmt"; break;
			case 127: s = "invalid Lhs"; break;
			case 128: s = "invalid Rhs"; break;
			case 129: s = "invalid Guard"; break;
			case 130: s = "invalid AttributeArg"; break;
			case 131: s = "invalid EquivOp"; break;
			case 132: s = "invalid ImpliesOp"; break;
			case 133: s = "invalid AndOp"; break;
			case 134: s = "invalid OrOp"; break;
			case 135: s = "invalid RelOp"; break;
			case 136: s = "invalid AddOp"; break;
			case 137: s = "invalid UnaryExpression"; break;
			case 138: s = "invalid MulOp"; break;
			case 139: s = "invalid NegOp"; break;
			case 140: s = "invalid EndlessExpression"; break;
			case 141: s = "invalid Suffix"; break;
			case 142: s = "invalid Suffix"; break;
			case 143: s = "invalid Suffix"; break;
			case 144: s = "invalid ConstAtomExpression"; break;
			case 145: s = "invalid QuantifierGuts"; break;
			case 146: s = "invalid Forall"; break;
			case 147: s = "invalid Exists"; break;
			case 148: s = "invalid AttributeOrTrigger"; break;
			case 149: s = "invalid QSep"; break;

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