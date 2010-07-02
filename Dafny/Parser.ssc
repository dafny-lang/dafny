using System.Collections.Generic;
using System.Numerics;
using Microsoft.Boogie;
using System.IO;
using System.Text;




using System;
using Microsoft.Contracts;

namespace Microsoft.Dafny {



public class Parser {
	public const int _EOF = 0;
	public const int _ident = 1;
	public const int _digits = 2;
	public const int _string = 3;
	public const int maxT = 103;

	const bool T = true;
	const bool x = false;
	const int minErrDist = 2;
	
	public Scanner/*!*/ scanner;
	public Errors/*!*/  errors;

	public Token/*!*/ t;    // last recognized token
	public Token/*!*/ la;   // lookahead token
	int errDist = minErrDist;

static List<ModuleDecl!>! theModules = new List<ModuleDecl!>();


static Expression! dummyExpr = new LiteralExpr(Token.NoToken);
static FrameExpression! dummyFrameExpr = new FrameExpression(dummyExpr, null);
static Statement! dummyStmt = new ReturnStmt(Token.NoToken);
static Attributes.Argument! dummyAttrArg = new Attributes.Argument("dummyAttrArg");
static Scope<string>! parseVarScope = new Scope<string>();
static int anonymousIds = 0;

struct MemberModifiers {
  public bool IsGhost;
  public bool IsStatic;
  public bool IsUnlimited;
}

// helper routine for parsing call statements
private static void RecordCallLhs(IdentifierExpr! e,
                                  List<IdentifierExpr!>! lhs,
                                  List<AutoVarDecl!>! newVars) {
  int index = lhs.Count;
  lhs.Add(e);
  if (parseVarScope.Find(e.Name) == null) {
    AutoVarDecl d = new AutoVarDecl(e.tok, e.Name, new InferredTypeProxy(), index);
    newVars.Add(d);
    parseVarScope.Push(e.Name, e.Name);
  }
}

// helper routine for parsing call statements
private static Expression! ConvertToLocal(Expression! e)
{
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
public static int Parse (string! filename, List<ModuleDecl!>! modules) /* throws System.IO.IOException */ {
  string s;
  if (filename == "stdin.dfy") {
    s = Microsoft.Boogie.ParserHelper.Fill(System.Console.In, new List<string!>());
    return Parse(s, filename, modules);
  } else {
    using (System.IO.StreamReader reader = new System.IO.StreamReader(filename)) {
      s = Microsoft.Boogie.ParserHelper.Fill(reader, new List<string!>());
      return Parse(s, filename, modules);
    }
  }
}

///<summary>
/// Parses top-level things (modules, classes, datatypes, class members)
/// and appends them in appropriate form to "modules".
/// Returns the number of parsing errors encountered.
/// Note: first initialize the Scanner.
///</summary>
public static int Parse (string! s, string! filename, List<ModuleDecl!>! modules) {
  List<ModuleDecl!> oldModules = theModules;
  theModules = modules;
  byte[]! buffer = (!) UTF8Encoding.Default.GetBytes(s);
  MemoryStream ms = new MemoryStream(buffer,false);
  Errors errors = new Errors();
  Scanner scanner = new Scanner(ms, errors, filename);
  Parser parser = new Parser(scanner, errors);
  parser.Parse();
  theModules = oldModules;
  return parser.errors.count;
}

/*--------------------------------------------------------------------------*/


	public Parser(Scanner/*!*/ scanner, Errors/*!*/ errors) {
		this.scanner = scanner;
		this.errors = errors;
		Token! tok = new Token();
		tok.val = "";
		this.la = tok;
		this.t = new Token(); // just to satisfy its non-null constraint
	}

	void SynErr (int n) {
		if (errDist >= minErrDist) errors.SynErr(la.filename, la.line, la.col, n);
		errDist = 0;
	}

	public void SemErr (string! msg) {
		if (errDist >= minErrDist) errors.SemErr(t, msg);
		errDist = 0;
	}
	
    public void SemErr(IToken! tok, string! msg) {
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
		ClassDecl! c; DatatypeDecl! dt;
		Attributes attrs;  IToken! id;  List<string!> theImports;
		
		     List<MemberDecl!> membersDefaultClass = new List<MemberDecl!>();
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
			if (la.kind == 4) {
				Get();
				attrs = null;  theImports = new List<string!>(); 
				while (la.kind == 6) {
					Attribute(ref attrs);
				}
				Ident(out id);
				if (la.kind == 5) {
					Get();
					Idents(theImports);
				}
				module = new ModuleDecl(id, id.val, theImports, attrs); 
				Expect(6);
				while (la.kind == 8 || la.kind == 13) {
					if (la.kind == 8) {
						ClassDecl(module, out c);
						module.TopLevelDecls.Add(c); 
					} else {
						DatatypeDecl(module, out dt);
						module.TopLevelDecls.Add(dt); 
					}
				}
				theModules.Add(module); 
				Expect(7);
			} else if (la.kind == 8) {
				ClassDecl(defaultModule, out c);
				defaultModule.TopLevelDecls.Add(c); 
			} else if (la.kind == 13) {
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
		Expect(6);
		AttributeBody(ref attrs);
		Expect(7);
	}

	void Ident(out IToken! x) {
		Expect(1);
		x = t; 
	}

	void Idents(List<string!>! ids) {
		IToken! id; 
		Ident(out id);
		ids.Add(id.val); 
		while (la.kind == 16) {
			Get();
			Ident(out id);
			ids.Add(id.val); 
		}
	}

	void ClassDecl(ModuleDecl! module, out ClassDecl! c) {
		IToken! id;
		Attributes attrs = null;
		List<TypeParameter!> typeArgs = new List<TypeParameter!>();
		IToken! idRefined;
		IToken optionalId = null;         
		List<MemberDecl!> members = new List<MemberDecl!>();
		
		Expect(8);
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 20) {
			GenericParameters(typeArgs);
		}
		if (la.kind == 9) {
			Get();
			Ident(out idRefined);
			optionalId = idRefined; 
		}
		Expect(6);
		while (StartOf(2)) {
			ClassMemberDecl(members);
		}
		Expect(7);
		if (optionalId == null)        
		 c = new ClassDecl(id, id.val, module, typeArgs, members, attrs); 
		else 
		  c = new ClassRefinementDecl(id, id.val, module, typeArgs, members, attrs, optionalId);
		
	}

	void DatatypeDecl(ModuleDecl! module, out DatatypeDecl! dt) {
		IToken! id;
		Attributes attrs = null;
		List<TypeParameter!> typeArgs = new List<TypeParameter!>();
		List<DatatypeCtor!> ctors = new List<DatatypeCtor!>();
		
		Expect(13);
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 20) {
			GenericParameters(typeArgs);
		}
		Expect(6);
		while (la.kind == 1 || la.kind == 6) {
			DatatypeMemberDecl(ctors);
		}
		Expect(7);
		dt = new DatatypeDecl(id, id.val, module, typeArgs, ctors, attrs); 
	}

	void ClassMemberDecl(List<MemberDecl!>! mm) {
		Method! m;
		Function! f;
		MemberModifiers mmod = new MemberModifiers();
		
		while (la.kind == 10 || la.kind == 11 || la.kind == 12) {
			if (la.kind == 10) {
				Get();
				mmod.IsGhost = true; 
			} else if (la.kind == 11) {
				Get();
				mmod.IsStatic = true; 
			} else {
				Get();
				mmod.IsUnlimited = true; 
			}
		}
		if (la.kind == 15) {
			FieldDecl(mmod, mm);
		} else if (la.kind == 37) {
			FunctionDecl(mmod, out f);
			mm.Add(f); 
		} else if (la.kind == 9 || la.kind == 22) {
			MethodDecl(mmod, out m);
			mm.Add(m); 
		} else if (la.kind == 17) {
			CouplingInvDecl(mmod, mm);
		} else SynErr(104);
	}

	void GenericParameters(List<TypeParameter!>! typeArgs) {
		IToken! id; 
		Expect(20);
		Ident(out id);
		typeArgs.Add(new TypeParameter(id, id.val)); 
		while (la.kind == 16) {
			Get();
			Ident(out id);
			typeArgs.Add(new TypeParameter(id, id.val)); 
		}
		Expect(21);
	}

	void FieldDecl(MemberModifiers mmod, List<MemberDecl!>! mm) {
		Attributes attrs = null;
		IToken! id;  Type! ty;
		
		Expect(15);
		if (mmod.IsUnlimited) { SemErr(t, "fields cannot be declared 'unlimited'"); }
		if (mmod.IsStatic) { SemErr(t, "fields cannot be declared 'static'"); }
		
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		IdentType(out id, out ty);
		mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		while (la.kind == 16) {
			Get();
			IdentType(out id, out ty);
			mm.Add(new Field(id, id.val, mmod.IsGhost, ty, attrs)); 
		}
		Expect(14);
	}

	void FunctionDecl(MemberModifiers mmod, out Function! f) {
		Attributes attrs = null;
		IToken! id;
		List<TypeParameter!> typeArgs = new List<TypeParameter!>();
		List<Formal!> formals = new List<Formal!>();
		Type! returnType;
		List<Expression!> reqs = new List<Expression!>();
		List<FrameExpression!> reads = new List<FrameExpression!>();
		List<Expression!> decreases = new List<Expression!>();
		Expression! bb;  Expression body = null;
		bool isFunctionMethod = false;
		
		Expect(37);
		if (la.kind == 22) {
			Get();
			isFunctionMethod = true; 
		}
		if (mmod.IsGhost) { SemErr(t, "functions cannot be declared 'ghost' (they are ghost by default)"); }
		
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 20) {
			GenericParameters(typeArgs);
		}
		parseVarScope.PushMarker(); 
		Formals(true, false, formals);
		Expect(19);
		Type(out returnType);
		if (la.kind == 14) {
			Get();
			while (la.kind == 26 || la.kind == 28 || la.kind == 38) {
				FunctionSpec(reqs, reads, decreases);
			}
		} else if (StartOf(3)) {
			while (la.kind == 26 || la.kind == 28 || la.kind == 38) {
				FunctionSpec(reqs, reads, decreases);
			}
			FunctionBody(out bb);
			body = bb; 
		} else SynErr(105);
		parseVarScope.PopMarker();
		f = new Function(id, id.val, mmod.IsStatic, !isFunctionMethod, mmod.IsUnlimited, typeArgs, formals, returnType, reqs, reads, decreases, body, attrs);
		
	}

	void MethodDecl(MemberModifiers mmod, out Method! m) {
		IToken! id;
		Attributes attrs = null;
		List<TypeParameter!>! typeArgs = new List<TypeParameter!>();
		List<Formal!> ins = new List<Formal!>();
		List<Formal!> outs = new List<Formal!>();
		List<MaybeFreeExpression!> req = new List<MaybeFreeExpression!>();
		List<FrameExpression!> mod = new List<FrameExpression!>();
		List<MaybeFreeExpression!> ens = new List<MaybeFreeExpression!>();
		List<Expression!> dec = new List<Expression!>();
		Statement! bb;  BlockStmt body = null;
		bool isRefinement = false;
		
		if (la.kind == 22) {
			Get();
		} else if (la.kind == 9) {
			Get();
			isRefinement = true; 
		} else SynErr(106);
		if (mmod.IsUnlimited) { SemErr(t, "methods cannot be declared 'unlimited'"); }
		
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 20) {
			GenericParameters(typeArgs);
		}
		parseVarScope.PushMarker(); 
		Formals(true, true, ins);
		if (la.kind == 23) {
			Get();
			Formals(false, true, outs);
		}
		if (la.kind == 14) {
			Get();
			while (StartOf(4)) {
				MethodSpec(req, mod, ens, dec);
			}
		} else if (StartOf(5)) {
			while (StartOf(4)) {
				MethodSpec(req, mod, ens, dec);
			}
			BlockStmt(out bb);
			body = (BlockStmt)bb; 
		} else SynErr(107);
		parseVarScope.PopMarker();
		if (isRefinement)
		  m = new MethodRefinement(id, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs, req, mod, ens, dec, body, attrs);
		else 
		  m = new Method(id, id.val, mmod.IsStatic, mmod.IsGhost, typeArgs, ins, outs, req, mod, ens, dec, body, attrs); 
		
	}

	void CouplingInvDecl(MemberModifiers mmod, List<MemberDecl!>! mm) {
		Attributes attrs = null;
		List<IToken!> ids = new List<IToken!>();;
		IToken! id;
		Expression! e;
		parseVarScope.PushMarker();
		
		Expect(17);
		if (mmod.IsUnlimited) { SemErr(t, "coupling invariants cannot be declared 'unlimited'"); }
		if (mmod.IsStatic) { SemErr(t, "coupling invariants cannot be declared 'static'"); }
		if (mmod.IsGhost) { SemErr(t, "coupling invariants cannot be declared 'ghost'"); }
		
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		ids.Add(id); parseVarScope.Push(id.val, id.val); 
		while (la.kind == 16) {
			Get();
			Ident(out id);
			ids.Add(id); parseVarScope.Push(id.val, id.val); 
		}
		Expect(18);
		Expression(out e);
		Expect(14);
		mm.Add(new CouplingInvariant(ids, e, attrs)); 
		parseVarScope.PopMarker();
		
	}

	void DatatypeMemberDecl(List<DatatypeCtor!>! ctors) {
		Attributes attrs = null;
		IToken! id;
		List<TypeParameter!> typeArgs = new List<TypeParameter!>();
		List<Formal!> formals = new List<Formal!>();
		
		while (la.kind == 6) {
			Attribute(ref attrs);
		}
		Ident(out id);
		if (la.kind == 20) {
			GenericParameters(typeArgs);
		}
		parseVarScope.PushMarker(); 
		if (la.kind == 29) {
			FormalsOptionalIds(formals);
		}
		parseVarScope.PopMarker();
		ctors.Add(new DatatypeCtor(id, id.val, typeArgs, formals, attrs));
		
		Expect(14);
	}

	void FormalsOptionalIds(List<Formal!>! formals) {
		IToken! id;  Type! ty;  string! name;  bool isGhost; 
		Expect(29);
		if (StartOf(6)) {
			TypeIdentOptional(out id, out name, out ty, out isGhost);
			formals.Add(new Formal(id, name, ty, true, isGhost));  parseVarScope.Push(name, name); 
			while (la.kind == 16) {
				Get();
				TypeIdentOptional(out id, out name, out ty, out isGhost);
				formals.Add(new Formal(id, name, ty, true, isGhost));  parseVarScope.Push(name, name); 
			}
		}
		Expect(30);
	}

	void IdentType(out IToken! id, out Type! ty) {
		Ident(out id);
		Expect(19);
		Type(out ty);
	}

	void Expression(out Expression! e) {
		IToken! x;  Expression! e0;  Expression! e1 = dummyExpr;
		e = dummyExpr;
		
		if (la.kind == 52) {
			Get();
			x = t; 
			Expression(out e);
			Expect(64);
			Expression(out e0);
			Expect(53);
			Expression(out e1);
			e = new ITEExpr(x, e, e0, e1); 
		} else if (StartOf(7)) {
			EquivExpression(out e);
		} else SynErr(108);
	}

	void GIdentType(bool allowGhost, out IToken! id, out Type! ty, out bool isGhost) {
		isGhost = false; 
		if (la.kind == 10) {
			Get();
			if (allowGhost) { isGhost = true; } else { SemErr(t, "formal cannot be declared 'ghost' in this context"); } 
		}
		IdentType(out id, out ty);
	}

	void Type(out Type! ty) {
		IToken! tok; 
		TypeAndToken(out tok, out ty);
	}

	void IdentTypeOptional(out BoundVar! var) {
		IToken! id;  Type! ty;  Type optType = null;
		
		Ident(out id);
		if (la.kind == 19) {
			Get();
			Type(out ty);
			optType = ty; 
		}
		var = new BoundVar(id, id.val, optType == null ? new InferredTypeProxy() : optType); 
	}

	void TypeIdentOptional(out IToken! id, out string! identName, out Type! ty, out bool isGhost) {
		string name = null;  isGhost = false; 
		if (la.kind == 10) {
			Get();
			isGhost = true; 
		}
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
		if (name != null) {
		 identName = name;
		} else {
		  identName = "#" + anonymousIds++;
		}
		
	}

	void TypeAndToken(out IToken! tok, out Type! ty) {
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type!>! gt;
		
		if (la.kind == 31) {
			Get();
			tok = t; 
		} else if (la.kind == 32) {
			Get();
			tok = t;  ty = new IntType(); 
		} else if (la.kind == 33) {
			Get();
			tok = t;  gt = new List<Type!>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("set type expects exactly one type argument");
			}
			ty = new SetType(gt[0]);
			
		} else if (la.kind == 34) {
			Get();
			tok = t;  gt = new List<Type!>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("seq type expects exactly one type argument");
			}
			ty = new SeqType(gt[0]);
			
		} else if (la.kind == 1 || la.kind == 35 || la.kind == 36) {
			ReferenceType(out tok, out ty);
		} else SynErr(109);
	}

	void Formals(bool incoming, bool allowGhosts, List<Formal!>! formals) {
		IToken! id;  Type! ty;  bool isGhost; 
		Expect(29);
		if (la.kind == 1 || la.kind == 10) {
			GIdentType(allowGhosts, out id, out ty, out isGhost);
			formals.Add(new Formal(id, id.val, ty, incoming, isGhost));  parseVarScope.Push(id.val, id.val); 
			while (la.kind == 16) {
				Get();
				GIdentType(allowGhosts, out id, out ty, out isGhost);
				formals.Add(new Formal(id, id.val, ty, incoming, isGhost));  parseVarScope.Push(id.val, id.val); 
			}
		}
		Expect(30);
	}

	void MethodSpec(List<MaybeFreeExpression!>! req, List<FrameExpression!>! mod, List<MaybeFreeExpression!>! ens,
List<Expression!>! decreases) {
		Expression! e;  FrameExpression! fe;  bool isFree = false;
		
		if (la.kind == 24) {
			Get();
			if (StartOf(8)) {
				FrameExpression(out fe);
				mod.Add(fe); 
				while (la.kind == 16) {
					Get();
					FrameExpression(out fe);
					mod.Add(fe); 
				}
			}
			Expect(14);
		} else if (la.kind == 25 || la.kind == 26 || la.kind == 27) {
			if (la.kind == 25) {
				Get();
				isFree = true; 
			}
			if (la.kind == 26) {
				Get();
				Expression(out e);
				Expect(14);
				req.Add(new MaybeFreeExpression(e, isFree)); 
			} else if (la.kind == 27) {
				Get();
				Expression(out e);
				Expect(14);
				ens.Add(new MaybeFreeExpression(e, isFree)); 
			} else SynErr(110);
		} else if (la.kind == 28) {
			Get();
			Expressions(decreases);
			Expect(14);
		} else SynErr(111);
	}

	void BlockStmt(out Statement! block) {
		IToken! x;
		List<Statement!> body = new List<Statement!>();
		Statement! s;
		
		parseVarScope.PushMarker(); 
		Expect(6);
		x = t; 
		while (StartOf(9)) {
			Stmt(body);
		}
		Expect(7);
		block = new BlockStmt(x, body); 
		parseVarScope.PopMarker(); 
	}

	void FrameExpression(out FrameExpression! fe) {
		Expression! e;  IToken! id;  string fieldName = null; 
		Expression(out e);
		if (la.kind == 40) {
			Get();
			Ident(out id);
			fieldName = id.val; 
		}
		fe = new FrameExpression(e, fieldName); 
	}

	void Expressions(List<Expression!>! args) {
		Expression! e; 
		Expression(out e);
		args.Add(e); 
		while (la.kind == 16) {
			Get();
			Expression(out e);
			args.Add(e); 
		}
	}

	void GenericInstantiation(List<Type!>! gt) {
		Type! ty; 
		Expect(20);
		Type(out ty);
		gt.Add(ty); 
		while (la.kind == 16) {
			Get();
			Type(out ty);
			gt.Add(ty); 
		}
		Expect(21);
	}

	void ReferenceType(out IToken! tok, out Type! ty) {
		tok = Token.NoToken;  ty = new BoolType();  /*keep compiler happy*/
		List<Type!>! gt;
		
		if (la.kind == 35) {
			Get();
			tok = t;  ty = new ObjectType(); 
		} else if (la.kind == 36) {
			Get();
			tok = t;  gt = new List<Type!>(); 
			GenericInstantiation(gt);
			if (gt.Count != 1) {
			 SemErr("array type expects exactly one type argument");
			}
			ty = UserDefinedType.ArrayType(tok, gt[0]);
			
		} else if (la.kind == 1) {
			Ident(out tok);
			gt = new List<Type!>(); 
			if (la.kind == 20) {
				GenericInstantiation(gt);
			}
			ty = new UserDefinedType(tok, tok.val, gt); 
		} else SynErr(112);
	}

	void FunctionSpec(List<Expression!>! reqs, List<FrameExpression!>! reads, List<Expression!>! decreases) {
		Expression! e;  FrameExpression! fe; 
		if (la.kind == 26) {
			Get();
			Expression(out e);
			Expect(14);
			reqs.Add(e); 
		} else if (la.kind == 38) {
			Get();
			if (StartOf(10)) {
				PossiblyWildFrameExpression(out fe);
				reads.Add(fe); 
				while (la.kind == 16) {
					Get();
					PossiblyWildFrameExpression(out fe);
					reads.Add(fe); 
				}
			}
			Expect(14);
		} else if (la.kind == 28) {
			Get();
			Expressions(decreases);
			Expect(14);
		} else SynErr(113);
	}

	void FunctionBody(out Expression! e) {
		e = dummyExpr; 
		Expect(6);
		if (la.kind == 41) {
			MatchExpression(out e);
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(114);
		Expect(7);
	}

	void PossiblyWildFrameExpression(out FrameExpression! fe) {
		fe = dummyFrameExpr; 
		if (la.kind == 39) {
			Get();
			fe = new FrameExpression(new WildcardExpr(t), null); 
		} else if (StartOf(8)) {
			FrameExpression(out fe);
		} else SynErr(115);
	}

	void PossiblyWildExpression(out Expression! e) {
		e = dummyExpr; 
		if (la.kind == 39) {
			Get();
			e = new WildcardExpr(t); 
		} else if (StartOf(8)) {
			Expression(out e);
		} else SynErr(116);
	}

	void MatchExpression(out Expression! e) {
		IToken! x;  MatchCaseExpr! c;
		List<MatchCaseExpr!> cases = new List<MatchCaseExpr!>();
		
		Expect(41);
		x = t; 
		Expression(out e);
		while (la.kind == 42) {
			CaseExpression(out c);
			cases.Add(c); 
		}
		e = new MatchExpr(x, e, cases); 
	}

	void CaseExpression(out MatchCaseExpr! c) {
		IToken! x, id, arg;
		List<BoundVar!> arguments = new List<BoundVar!>();
		Expression! body;
		
		Expect(42);
		x = t;  parseVarScope.PushMarker(); 
		Ident(out id);
		if (la.kind == 29) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy()));
			parseVarScope.Push(arg.val, arg.val); 
			while (la.kind == 16) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy()));
				parseVarScope.Push(arg.val, arg.val); 
			}
			Expect(30);
		}
		Expect(43);
		Expression(out body);
		c = new MatchCaseExpr(x, id.val, arguments, body);
		parseVarScope.PopMarker(); 
	}

	void Stmt(List<Statement!>! ss) {
		Statement! s; 
		while (la.kind == 6) {
			BlockStmt(out s);
			ss.Add(s); 
		}
		if (StartOf(11)) {
			OneStmt(out s);
			ss.Add(s); 
		} else if (la.kind == 10 || la.kind == 15) {
			VarDeclStmts(ss);
		} else SynErr(117);
	}

	void OneStmt(out Statement! s) {
		IToken! x;  IToken! id;  string label = null;
		s = dummyStmt;  /* to please the compiler */
		
		switch (la.kind) {
		case 60: {
			AssertStmt(out s);
			break;
		}
		case 61: {
			AssumeStmt(out s);
			break;
		}
		case 62: {
			UseStmt(out s);
			break;
		}
		case 63: {
			PrintStmt(out s);
			break;
		}
		case 1: case 29: case 95: case 96: {
			AssignStmt(out s);
			break;
		}
		case 51: {
			HavocStmt(out s);
			break;
		}
		case 56: {
			CallStmt(out s);
			break;
		}
		case 52: {
			IfStmt(out s);
			break;
		}
		case 54: {
			WhileStmt(out s);
			break;
		}
		case 41: {
			MatchStmt(out s);
			break;
		}
		case 57: {
			ForeachStmt(out s);
			break;
		}
		case 44: {
			Get();
			x = t; 
			Ident(out id);
			Expect(19);
			s = new LabelStmt(x, id.val); 
			break;
		}
		case 45: {
			Get();
			x = t; 
			if (la.kind == 1) {
				Ident(out id);
				label = id.val; 
			}
			Expect(14);
			s = new BreakStmt(x, label); 
			break;
		}
		case 46: {
			Get();
			x = t; 
			Expect(14);
			s = new ReturnStmt(x); 
			break;
		}
		default: SynErr(118); break;
		}
	}

	void VarDeclStmts(List<Statement!>! ss) {
		VarDecl! d;  bool isGhost = false; 
		if (la.kind == 10) {
			Get();
			isGhost = true; 
		}
		Expect(15);
		IdentTypeRhs(out d, isGhost);
		ss.Add(d);  parseVarScope.Push(d.Name, d.Name); 
		while (la.kind == 16) {
			Get();
			IdentTypeRhs(out d, isGhost);
			ss.Add(d);  parseVarScope.Push(d.Name, d.Name); 
		}
		Expect(14);
	}

	void AssertStmt(out Statement! s) {
		IToken! x;  Expression! e; 
		Expect(60);
		x = t; 
		Expression(out e);
		Expect(14);
		s = new AssertStmt(x, e); 
	}

	void AssumeStmt(out Statement! s) {
		IToken! x;  Expression! e; 
		Expect(61);
		x = t; 
		Expression(out e);
		Expect(14);
		s = new AssumeStmt(x, e); 
	}

	void UseStmt(out Statement! s) {
		IToken! x;  Expression! e; 
		Expect(62);
		x = t; 
		Expression(out e);
		Expect(14);
		s = new UseStmt(x, e); 
	}

	void PrintStmt(out Statement! s) {
		IToken! x;  Attributes.Argument! arg;
		List<Attributes.Argument!> args = new List<Attributes.Argument!>();
		
		Expect(63);
		x = t; 
		AttributeArg(out arg);
		args.Add(arg); 
		while (la.kind == 16) {
			Get();
			AttributeArg(out arg);
			args.Add(arg); 
		}
		Expect(14);
		s = new PrintStmt(x, args); 
	}

	void AssignStmt(out Statement! s) {
		IToken! x;
		Expression! lhs;
		Expression rhs;
		Type ty;
		s = dummyStmt;
		
		LhsExpr(out lhs);
		Expect(47);
		x = t; 
		AssignRhs(out rhs, out ty);
		if (ty == null) {
		 assert rhs != null;
		 s = new AssignStmt(x, lhs, rhs);
		} else if (rhs == null) {
		  s = new AssignStmt(x, lhs, ty);
		} else {
		  s = new AssignStmt(x, lhs, ty, rhs);
		}
		
		Expect(14);
	}

	void HavocStmt(out Statement! s) {
		IToken! x;  Expression! lhs; 
		Expect(51);
		x = t; 
		LhsExpr(out lhs);
		Expect(14);
		s = new AssignStmt(x, lhs); 
	}

	void CallStmt(out Statement! s) {
		IToken! x, id;
		Expression! e;
		List<IdentifierExpr!> lhs = new List<IdentifierExpr!>();
		List<AutoVarDecl!> newVars = new List<AutoVarDecl!>();
		
		Expect(56);
		x = t; 
		CallStmtSubExpr(out e);
		if (la.kind == 16 || la.kind == 47) {
			if (la.kind == 16) {
				Get();
				e = ConvertToLocal(e);
				if (e is IdentifierExpr) {
				  RecordCallLhs((IdentifierExpr)e, lhs, newVars);
				} else if (e is FieldSelectExpr) {
				  SemErr(e.tok, "each LHS of call statement must be a variable, not a field");
				} else {
				  SemErr(e.tok, "each LHS of call statement must be a variable");
				}
				
				Ident(out id);
				RecordCallLhs(new IdentifierExpr(id, id.val), lhs, newVars); 
				while (la.kind == 16) {
					Get();
					Ident(out id);
					RecordCallLhs(new IdentifierExpr(id, id.val), lhs, newVars); 
				}
				Expect(47);
				CallStmtSubExpr(out e);
			} else {
				Get();
				e = ConvertToLocal(e);
				if (e is IdentifierExpr) {
				  RecordCallLhs((IdentifierExpr)e, lhs, newVars);
				} else if (e is FieldSelectExpr) {
				  SemErr(e.tok, "each LHS of call statement must be a variable, not a field");
				} else {
				  SemErr(e.tok, "each LHS of call statement must be a variable");
				}
				
				CallStmtSubExpr(out e);
			}
		}
		Expect(14);
		if (e is FunctionCallExpr) {
		 FunctionCallExpr fce = (FunctionCallExpr)e;
		 s = new CallStmt(x, newVars, lhs, fce.Receiver, fce.Name, fce.Args);  // this actually does an ownership transfer of fce.Args
		} else {
		  SemErr("RHS of call statement must denote a method invocation");
		  s = new CallStmt(x, newVars, lhs, dummyExpr, "dummyMethodName", new List<Expression!>());
		}
		
	}

	void IfStmt(out Statement! ifStmt) {
		IToken! x;
		Expression guard;
		Statement! thn;
		Statement! s;
		Statement els = null;
		
		Expect(52);
		x = t; 
		Guard(out guard);
		BlockStmt(out thn);
		if (la.kind == 53) {
			Get();
			if (la.kind == 52) {
				IfStmt(out s);
				els = s; 
			} else if (la.kind == 6) {
				BlockStmt(out s);
				els = s; 
			} else SynErr(119);
		}
		ifStmt = new IfStmt(x, guard, thn, els); 
	}

	void WhileStmt(out Statement! stmt) {
		IToken! x;
		Expression guard;
		bool isFree;  Expression! e;
		List<MaybeFreeExpression!> invariants = new List<MaybeFreeExpression!>();
		List<Expression!> decreases = new List<Expression!>();
		Statement! body;
		
		Expect(54);
		x = t; 
		Guard(out guard);
		assume guard == null || Owner.None(guard); 
		while (la.kind == 25 || la.kind == 28 || la.kind == 55) {
			if (la.kind == 25 || la.kind == 55) {
				isFree = false; 
				if (la.kind == 25) {
					Get();
					isFree = true; 
				}
				Expect(55);
				Expression(out e);
				invariants.Add(new MaybeFreeExpression(e, isFree)); 
				Expect(14);
			} else {
				Get();
				PossiblyWildExpression(out e);
				decreases.Add(e); 
				while (la.kind == 16) {
					Get();
					PossiblyWildExpression(out e);
					decreases.Add(e); 
				}
				Expect(14);
			}
		}
		BlockStmt(out body);
		stmt = new WhileStmt(x, guard, invariants, decreases, body); 
	}

	void MatchStmt(out Statement! s) {
		Token x;  Expression! e;  MatchCaseStmt! c;
		List<MatchCaseStmt!> cases = new List<MatchCaseStmt!>(); 
		Expect(41);
		x = t; 
		Expression(out e);
		Expect(6);
		while (la.kind == 42) {
			CaseStatement(out c);
			cases.Add(c); 
		}
		Expect(7);
		s = new MatchStmt(x, e, cases); 
	}

	void ForeachStmt(out Statement! s) {
		IToken! x, boundVar;
		Type! ty;
		Expression! collection;
		Expression! range;
		List<PredicateStmt!> bodyPrefix = new List<PredicateStmt!>();
		AssignStmt bodyAssign = null;
		
		parseVarScope.PushMarker(); 
		Expect(57);
		x = t;
		range = new LiteralExpr(x, true);
		ty = new InferredTypeProxy();
		
		Expect(29);
		Ident(out boundVar);
		if (la.kind == 19) {
			Get();
			Type(out ty);
		}
		Expect(58);
		Expression(out collection);
		parseVarScope.Push(boundVar.val, boundVar.val); 
		if (la.kind == 59) {
			Get();
			Expression(out range);
		}
		Expect(30);
		Expect(6);
		while (la.kind == 60 || la.kind == 61 || la.kind == 62) {
			if (la.kind == 60) {
				AssertStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			} else if (la.kind == 61) {
				AssumeStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			} else {
				UseStmt(out s);
				if (s is PredicateStmt) { bodyPrefix.Add((PredicateStmt)s); } 
			}
		}
		if (StartOf(12)) {
			AssignStmt(out s);
			if (s is AssignStmt) { bodyAssign = (AssignStmt)s; } 
		} else if (la.kind == 51) {
			HavocStmt(out s);
			if (s is AssignStmt) { bodyAssign = (AssignStmt)s; } 
		} else SynErr(120);
		Expect(7);
		if (bodyAssign != null) {
		 s = new ForeachStmt(x, new BoundVar(boundVar, boundVar.val, ty), collection, range, bodyPrefix, bodyAssign);
		} else {
		  s = dummyStmt;  // some error occurred in parsing the bodyAssign
		}
		
		parseVarScope.PopMarker(); 
	}

	void LhsExpr(out Expression! e) {
		SelectExpression(out e);
	}

	void AssignRhs(out Expression e, out Type ty) {
		IToken! x;  Expression! ee;  Type! tt;
		e = null;  ty = null;
		
		if (la.kind == 48) {
			Get();
			TypeAndToken(out x, out tt);
			ty = tt; 
			if (la.kind == 49) {
				Get();
				Expression(out ee);
				Expect(50);
				e = ee; 
			}
		} else if (StartOf(8)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(121);
		if (e == null && ty == null) { e = dummyExpr; } 
	}

	void SelectExpression(out Expression! e) {
		IToken! id;  e = dummyExpr; 
		if (la.kind == 1) {
			IdentOrFuncExpression(out e);
		} else if (la.kind == 29 || la.kind == 95 || la.kind == 96) {
			ObjectExpression(out e);
		} else SynErr(122);
		while (la.kind == 49 || la.kind == 92) {
			SelectOrCallSuffix(ref e);
		}
	}

	void IdentTypeRhs(out VarDecl! d, bool isGhost) {
		IToken! id;  Type! ty;  Expression! e;
		Expression rhs = null;  Type newType = null;
		Type optionalType = null;  DeterminedAssignmentRhs optionalRhs = null;
		
		Ident(out id);
		if (la.kind == 19) {
			Get();
			Type(out ty);
			optionalType = ty; 
		}
		if (la.kind == 47) {
			Get();
			AssignRhs(out rhs, out newType);
		}
		if (newType == null && rhs != null) {
		 optionalRhs = new ExprRhs(rhs);
		} else if (newType != null) {
		  if (rhs == null) {
		    optionalRhs = new TypeRhs(newType);
		  } else {
		    optionalRhs = new TypeRhs(newType, rhs);
		  }
		} else if (optionalType == null) {
		  optionalType = new InferredTypeProxy();
		}
		d = new VarDecl(id, id.val, optionalType, isGhost, optionalRhs);
		
	}

	void Guard(out Expression e) {
		Expression! ee;  e = null; 
		Expect(29);
		if (la.kind == 39) {
			Get();
			e = null; 
		} else if (StartOf(8)) {
			Expression(out ee);
			e = ee; 
		} else SynErr(123);
		Expect(30);
	}

	void CaseStatement(out MatchCaseStmt! c) {
		IToken! x, id, arg;
		List<BoundVar!> arguments = new List<BoundVar!>();
		List<Statement!> body = new List<Statement!>();
		
		Expect(42);
		x = t;  parseVarScope.PushMarker(); 
		Ident(out id);
		if (la.kind == 29) {
			Get();
			Ident(out arg);
			arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy()));
			parseVarScope.Push(arg.val, arg.val); 
			while (la.kind == 16) {
				Get();
				Ident(out arg);
				arguments.Add(new BoundVar(arg, arg.val, new InferredTypeProxy()));
				parseVarScope.Push(arg.val, arg.val); 
			}
			Expect(30);
		}
		Expect(43);
		parseVarScope.PushMarker(); 
		while (StartOf(9)) {
			Stmt(body);
		}
		parseVarScope.PopMarker(); 
		c = new MatchCaseStmt(x, id.val, arguments, body); 
		parseVarScope.PopMarker(); 
	}

	void CallStmtSubExpr(out Expression! e) {
		e = dummyExpr; 
		if (la.kind == 1) {
			IdentOrFuncExpression(out e);
		} else if (la.kind == 29 || la.kind == 95 || la.kind == 96) {
			ObjectExpression(out e);
			SelectOrCallSuffix(ref e);
		} else SynErr(124);
		while (la.kind == 49 || la.kind == 92) {
			SelectOrCallSuffix(ref e);
		}
	}

	void AttributeArg(out Attributes.Argument! arg) {
		Expression! e;  arg = dummyAttrArg; 
		if (la.kind == 3) {
			Get();
			arg = new Attributes.Argument(t.val.Substring(1, t.val.Length-2)); 
		} else if (StartOf(8)) {
			Expression(out e);
			arg = new Attributes.Argument(e); 
		} else SynErr(125);
	}

	void EquivExpression(out Expression! e0) {
		IToken! x;  Expression! e1; 
		ImpliesExpression(out e0);
		while (la.kind == 65 || la.kind == 66) {
			EquivOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Iff, e0, e1); 
		}
	}

	void ImpliesExpression(out Expression! e0) {
		IToken! x;  Expression! e1; 
		LogicalExpression(out e0);
		if (la.kind == 67 || la.kind == 68) {
			ImpliesOp();
			x = t; 
			ImpliesExpression(out e1);
			e0 = new BinaryExpr(x, BinaryExpr.Opcode.Imp, e0, e1); 
		}
	}

	void EquivOp() {
		if (la.kind == 65) {
			Get();
		} else if (la.kind == 66) {
			Get();
		} else SynErr(126);
	}

	void LogicalExpression(out Expression! e0) {
		IToken! x;  Expression! e1; 
		RelationalExpression(out e0);
		if (StartOf(13)) {
			if (la.kind == 69 || la.kind == 70) {
				AndOp();
				x = t; 
				RelationalExpression(out e1);
				e0 = new BinaryExpr(x, BinaryExpr.Opcode.And, e0, e1); 
				while (la.kind == 69 || la.kind == 70) {
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
				while (la.kind == 71 || la.kind == 72) {
					OrOp();
					x = t; 
					RelationalExpression(out e1);
					e0 = new BinaryExpr(x, BinaryExpr.Opcode.Or, e0, e1); 
				}
			}
		}
	}

	void ImpliesOp() {
		if (la.kind == 67) {
			Get();
		} else if (la.kind == 68) {
			Get();
		} else SynErr(127);
	}

	void RelationalExpression(out Expression! e0) {
		IToken! x;  Expression! e1;  BinaryExpr.Opcode op; 
		Term(out e0);
		if (StartOf(14)) {
			RelOp(out x, out op);
			Term(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AndOp() {
		if (la.kind == 69) {
			Get();
		} else if (la.kind == 70) {
			Get();
		} else SynErr(128);
	}

	void OrOp() {
		if (la.kind == 71) {
			Get();
		} else if (la.kind == 72) {
			Get();
		} else SynErr(129);
	}

	void Term(out Expression! e0) {
		IToken! x;  Expression! e1;  BinaryExpr.Opcode op; 
		Factor(out e0);
		while (la.kind == 82 || la.kind == 83) {
			AddOp(out x, out op);
			Factor(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void RelOp(out IToken! x, out BinaryExpr.Opcode op) {
		x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		switch (la.kind) {
		case 73: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Eq; 
			break;
		}
		case 20: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Lt; 
			break;
		}
		case 21: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Gt; 
			break;
		}
		case 74: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 75: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		case 76: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 77: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Disjoint; 
			break;
		}
		case 58: {
			Get();
			x = t;  op = BinaryExpr.Opcode.In; 
			break;
		}
		case 78: {
			Get();
			x = t;  op = BinaryExpr.Opcode.NotIn; 
			break;
		}
		case 79: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Neq; 
			break;
		}
		case 80: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Le; 
			break;
		}
		case 81: {
			Get();
			x = t;  op = BinaryExpr.Opcode.Ge; 
			break;
		}
		default: SynErr(130); break;
		}
	}

	void Factor(out Expression! e0) {
		IToken! x;  Expression! e1;  BinaryExpr.Opcode op; 
		UnaryExpression(out e0);
		while (la.kind == 39 || la.kind == 84 || la.kind == 85) {
			MulOp(out x, out op);
			UnaryExpression(out e1);
			e0 = new BinaryExpr(x, op, e0, e1); 
		}
	}

	void AddOp(out IToken! x, out BinaryExpr.Opcode op) {
		x = Token.NoToken;  op=BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 82) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Add; 
		} else if (la.kind == 83) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Sub; 
		} else SynErr(131);
	}

	void UnaryExpression(out Expression! e) {
		IToken! x;  e = dummyExpr; 
		if (la.kind == 83) {
			Get();
			x = t; 
			UnaryExpression(out e);
			e = new BinaryExpr(x, BinaryExpr.Opcode.Sub, new LiteralExpr(x, 0), e); 
		} else if (la.kind == 86 || la.kind == 87) {
			NegOp();
			x = t; 
			UnaryExpression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.Not, e); 
		} else if (StartOf(12)) {
			SelectExpression(out e);
		} else if (StartOf(15)) {
			ConstAtomExpression(out e);
		} else SynErr(132);
	}

	void MulOp(out IToken! x, out BinaryExpr.Opcode op) {
		x = Token.NoToken;  op = BinaryExpr.Opcode.Add/*(dummy)*/; 
		if (la.kind == 39) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mul; 
		} else if (la.kind == 84) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Div; 
		} else if (la.kind == 85) {
			Get();
			x = t;  op = BinaryExpr.Opcode.Mod; 
		} else SynErr(133);
	}

	void NegOp() {
		if (la.kind == 86) {
			Get();
		} else if (la.kind == 87) {
			Get();
		} else SynErr(134);
	}

	void ConstAtomExpression(out Expression! e) {
		IToken! x, dtName, id;  BigInteger n;  List<Expression!>! elements;
		e = dummyExpr;  
		
		switch (la.kind) {
		case 88: {
			Get();
			e = new LiteralExpr(t, false); 
			break;
		}
		case 89: {
			Get();
			e = new LiteralExpr(t, true); 
			break;
		}
		case 90: {
			Get();
			e = new LiteralExpr(t); 
			break;
		}
		case 2: {
			Nat(out n);
			e = new LiteralExpr(t, n); 
			break;
		}
		case 91: {
			Get();
			x = t; 
			Ident(out dtName);
			Expect(92);
			Ident(out id);
			elements = new List<Expression!>(); 
			if (la.kind == 29) {
				Get();
				if (StartOf(8)) {
					Expressions(elements);
				}
				Expect(30);
			}
			e = new DatatypeValue(t, dtName.val, id.val, elements); 
			break;
		}
		case 93: {
			Get();
			x = t; 
			Expect(29);
			Expression(out e);
			Expect(30);
			e = new FreshExpr(x, e); 
			break;
		}
		case 59: {
			Get();
			x = t; 
			Expression(out e);
			e = new UnaryExpr(x, UnaryExpr.Opcode.SeqLength, e); 
			Expect(59);
			break;
		}
		case 6: {
			Get();
			x = t;  elements = new List<Expression!>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SetDisplayExpr(x, elements); 
			Expect(7);
			break;
		}
		case 49: {
			Get();
			x = t;  elements = new List<Expression!>(); 
			if (StartOf(8)) {
				Expressions(elements);
			}
			e = new SeqDisplayExpr(x, elements); 
			Expect(50);
			break;
		}
		default: SynErr(135); break;
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

	void IdentOrFuncExpression(out Expression! e) {
		IToken! id;  e = dummyExpr;  List<Expression!>! args; 
		Ident(out id);
		if (la.kind == 29) {
			Get();
			args = new List<Expression!>(); 
			if (StartOf(8)) {
				Expressions(args);
			}
			Expect(30);
			e = new FunctionCallExpr(id, id.val, new ImplicitThisExpr(id), args); 
		}
		if (e == dummyExpr) {
		 if (parseVarScope.Find(id.val) != null) {
		   e = new IdentifierExpr(id, id.val);
		 } else {
		   e = new FieldSelectExpr(id, new ImplicitThisExpr(id), id.val);
		 }
		}
		
	}

	void ObjectExpression(out Expression! e) {
		IToken! x;  e = dummyExpr; 
		if (la.kind == 95) {
			Get();
			e = new ThisExpr(t); 
		} else if (la.kind == 96) {
			Get();
			x = t; 
			Expect(29);
			Expression(out e);
			Expect(30);
			e = new OldExpr(x, e); 
		} else if (la.kind == 29) {
			Get();
			if (StartOf(16)) {
				QuantifierGuts(out e);
			} else if (StartOf(8)) {
				Expression(out e);
			} else SynErr(136);
			Expect(30);
		} else SynErr(137);
	}

	void SelectOrCallSuffix(ref Expression! e) {
		IToken! id, x;  List<Expression!>! args;
		Expression e0 = null;  Expression e1 = null;  Expression! ee;  bool anyDots = false;
		bool func = false;
		
		if (la.kind == 92) {
			Get();
			Ident(out id);
			if (la.kind == 29) {
				Get();
				args = new List<Expression!>();  func = true; 
				if (StartOf(8)) {
					Expressions(args);
				}
				Expect(30);
				e = new FunctionCallExpr(id, id.val, e, args); 
			}
			if (!func) { e = new FieldSelectExpr(id, e, id.val); } 
		} else if (la.kind == 49) {
			Get();
			x = t; 
			if (StartOf(8)) {
				Expression(out ee);
				e0 = ee; 
				if (la.kind == 47 || la.kind == 94) {
					if (la.kind == 94) {
						Get();
						anyDots = true; 
						if (StartOf(8)) {
							Expression(out ee);
							e1 = ee; 
						}
					} else {
						Get();
						Expression(out ee);
						e1 = ee; 
					}
				}
			} else if (la.kind == 94) {
				Get();
				Expression(out ee);
				anyDots = true;  e1 = ee; 
			} else SynErr(138);
			if (!anyDots && e0 == null) {
			 /* a parsing error occurred */
			 e0 = dummyExpr;
			}
			assert !anyDots ==> e0 != null;
			if (anyDots) {
			  assert e0 != null || e1 != null;
			  e = new SeqSelectExpr(x, false, e, e0, e1);
			} else if (e1 == null) {
			  assert e0 != null;
			  e = new SeqSelectExpr(x, true, e, e0, null);
			} else {
			  assert e0 != null;
			  e = new SeqUpdateExpr(x, e, e0, e1);
			}
			
			Expect(50);
		} else SynErr(139);
	}

	void QuantifierGuts(out Expression! q) {
		IToken! x = Token.NoToken;
		bool univ = false;
		BoundVar! bv;
		List<BoundVar!> bvars = new List<BoundVar!>();
		IToken! tok;  Expr! e;  ExprSeq! es;
		Attributes attrs = null;
		Triggers trigs = null;
		Expression! body;
		
		if (la.kind == 97 || la.kind == 98) {
			Forall();
			x = t;  univ = true; 
		} else if (la.kind == 99 || la.kind == 100) {
			Exists();
			x = t; 
		} else SynErr(140);
		parseVarScope.PushMarker(); 
		IdentTypeOptional(out bv);
		bvars.Add(bv);  parseVarScope.Push(bv.Name, bv.Name); 
		while (la.kind == 16) {
			Get();
			IdentTypeOptional(out bv);
			bvars.Add(bv);  parseVarScope.Push(bv.Name, bv.Name); 
		}
		while (la.kind == 6) {
			AttributeOrTrigger(ref attrs, ref trigs);
		}
		QSep();
		Expression(out body);
		if (univ) {
		 q = new ForallExpr(x, bvars, body, trigs, attrs);
		} else {
		  q = new ExistsExpr(x, bvars, body, trigs, attrs);
		}
		parseVarScope.PopMarker();
		
	}

	void Forall() {
		if (la.kind == 97) {
			Get();
		} else if (la.kind == 98) {
			Get();
		} else SynErr(141);
	}

	void Exists() {
		if (la.kind == 99) {
			Get();
		} else if (la.kind == 100) {
			Get();
		} else SynErr(142);
	}

	void AttributeOrTrigger(ref Attributes attrs, ref Triggers trigs) {
		List<Expression!> es = new List<Expression!>();
		
		Expect(6);
		if (la.kind == 19) {
			AttributeBody(ref attrs);
		} else if (StartOf(8)) {
			es = new List<Expression!>(); 
			Expressions(es);
			trigs = new Triggers(es, trigs); 
		} else SynErr(143);
		Expect(7);
	}

	void QSep() {
		if (la.kind == 101) {
			Get();
		} else if (la.kind == 102) {
			Get();
		} else SynErr(144);
	}

	void AttributeBody(ref Attributes attrs) {
		string aName;
		List<Attributes.Argument!> aArgs = new List<Attributes.Argument!>();
		Attributes.Argument! aArg;
		
		Expect(19);
		Expect(1);
		aName = t.val; 
		if (StartOf(17)) {
			AttributeArg(out aArg);
			aArgs.Add(aArg); 
			while (la.kind == 16) {
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
	
	static readonly bool[,]! set = {
		{T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, T,x,x,x, T,T,T,T, T,T,x,T, x,T,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,T, x,T,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, T,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,T,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,T,T,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,T,T, T,T,T,T, x,T,x,T, T,x,x,x, x,x,x,x, x},
		{x,T,T,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,T,T, T,T,T,T, x,T,x,T, T,x,x,x, x,x,x,x, x},
		{x,T,x,x, x,x,T,x, x,x,T,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,x, x,x,x,T, T,x,T,x, T,T,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x},
		{x,T,T,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,T,x,x, T,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,T,T, T,T,T,T, x,T,x,T, T,x,x,x, x,x,x,x, x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,T,T,x, x,x,x,T, T,x,T,x, T,T,x,x, T,T,T,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x},
		{x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, T,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,T,T,T, T,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,T,x, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, T,T,T,T, x,T,x,x, x,x,x,x, x,x,x,x, x},
		{x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,T,T, T,x,x,x, x},
		{x,T,T,T, x,x,T,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,T,x,x, T,x,x,x, x,x,x,T, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,x, x,x,x,T, x,x,T,T, T,T,T,T, x,T,x,T, T,x,x,x, x,x,x,x, x}

	};
} // end Parser


public class Errors {
	public int count = 0;                                    // number of errors detected
	public System.IO.TextWriter! errorStream = Console.Out;   // error messages go to this stream
//  public string errMsgFormat = "-- line {0} col {1}: {2}"; // 0=line, 1=column, 2=text
  public string! errMsgFormat4 = "{0}({1},{2}): Error: {3}"; // 0=line, 1=column, 2=text
  public string! errMsgFormat = "-- line {0} col {1}: {2}"; // 0=line, 1=column, 2=text
  
	public void SynErr (string filename, int line, int col, int n) {
		string s;
		Console.Write("{0}({1},{2}): syntax error: ", filename, line, col);
		switch (n) {
			case 0: s = "EOF expected"; break;
			case 1: s = "ident expected"; break;
			case 2: s = "digits expected"; break;
			case 3: s = "string expected"; break;
			case 4: s = "\"module\" expected"; break;
			case 5: s = "\"imports\" expected"; break;
			case 6: s = "\"{\" expected"; break;
			case 7: s = "\"}\" expected"; break;
			case 8: s = "\"class\" expected"; break;
			case 9: s = "\"refines\" expected"; break;
			case 10: s = "\"ghost\" expected"; break;
			case 11: s = "\"static\" expected"; break;
			case 12: s = "\"unlimited\" expected"; break;
			case 13: s = "\"datatype\" expected"; break;
			case 14: s = "\";\" expected"; break;
			case 15: s = "\"var\" expected"; break;
			case 16: s = "\",\" expected"; break;
			case 17: s = "\"replaces\" expected"; break;
			case 18: s = "\"by\" expected"; break;
			case 19: s = "\":\" expected"; break;
			case 20: s = "\"<\" expected"; break;
			case 21: s = "\">\" expected"; break;
			case 22: s = "\"method\" expected"; break;
			case 23: s = "\"returns\" expected"; break;
			case 24: s = "\"modifies\" expected"; break;
			case 25: s = "\"free\" expected"; break;
			case 26: s = "\"requires\" expected"; break;
			case 27: s = "\"ensures\" expected"; break;
			case 28: s = "\"decreases\" expected"; break;
			case 29: s = "\"(\" expected"; break;
			case 30: s = "\")\" expected"; break;
			case 31: s = "\"bool\" expected"; break;
			case 32: s = "\"int\" expected"; break;
			case 33: s = "\"set\" expected"; break;
			case 34: s = "\"seq\" expected"; break;
			case 35: s = "\"object\" expected"; break;
			case 36: s = "\"array\" expected"; break;
			case 37: s = "\"function\" expected"; break;
			case 38: s = "\"reads\" expected"; break;
			case 39: s = "\"*\" expected"; break;
			case 40: s = "\"`\" expected"; break;
			case 41: s = "\"match\" expected"; break;
			case 42: s = "\"case\" expected"; break;
			case 43: s = "\"=>\" expected"; break;
			case 44: s = "\"label\" expected"; break;
			case 45: s = "\"break\" expected"; break;
			case 46: s = "\"return\" expected"; break;
			case 47: s = "\":=\" expected"; break;
			case 48: s = "\"new\" expected"; break;
			case 49: s = "\"[\" expected"; break;
			case 50: s = "\"]\" expected"; break;
			case 51: s = "\"havoc\" expected"; break;
			case 52: s = "\"if\" expected"; break;
			case 53: s = "\"else\" expected"; break;
			case 54: s = "\"while\" expected"; break;
			case 55: s = "\"invariant\" expected"; break;
			case 56: s = "\"call\" expected"; break;
			case 57: s = "\"foreach\" expected"; break;
			case 58: s = "\"in\" expected"; break;
			case 59: s = "\"|\" expected"; break;
			case 60: s = "\"assert\" expected"; break;
			case 61: s = "\"assume\" expected"; break;
			case 62: s = "\"use\" expected"; break;
			case 63: s = "\"print\" expected"; break;
			case 64: s = "\"then\" expected"; break;
			case 65: s = "\"<==>\" expected"; break;
			case 66: s = "\"\\u21d4\" expected"; break;
			case 67: s = "\"==>\" expected"; break;
			case 68: s = "\"\\u21d2\" expected"; break;
			case 69: s = "\"&&\" expected"; break;
			case 70: s = "\"\\u2227\" expected"; break;
			case 71: s = "\"||\" expected"; break;
			case 72: s = "\"\\u2228\" expected"; break;
			case 73: s = "\"==\" expected"; break;
			case 74: s = "\"<=\" expected"; break;
			case 75: s = "\">=\" expected"; break;
			case 76: s = "\"!=\" expected"; break;
			case 77: s = "\"!!\" expected"; break;
			case 78: s = "\"!in\" expected"; break;
			case 79: s = "\"\\u2260\" expected"; break;
			case 80: s = "\"\\u2264\" expected"; break;
			case 81: s = "\"\\u2265\" expected"; break;
			case 82: s = "\"+\" expected"; break;
			case 83: s = "\"-\" expected"; break;
			case 84: s = "\"/\" expected"; break;
			case 85: s = "\"%\" expected"; break;
			case 86: s = "\"!\" expected"; break;
			case 87: s = "\"\\u00ac\" expected"; break;
			case 88: s = "\"false\" expected"; break;
			case 89: s = "\"true\" expected"; break;
			case 90: s = "\"null\" expected"; break;
			case 91: s = "\"#\" expected"; break;
			case 92: s = "\".\" expected"; break;
			case 93: s = "\"fresh\" expected"; break;
			case 94: s = "\"..\" expected"; break;
			case 95: s = "\"this\" expected"; break;
			case 96: s = "\"old\" expected"; break;
			case 97: s = "\"forall\" expected"; break;
			case 98: s = "\"\\u2200\" expected"; break;
			case 99: s = "\"exists\" expected"; break;
			case 100: s = "\"\\u2203\" expected"; break;
			case 101: s = "\"::\" expected"; break;
			case 102: s = "\"\\u2022\" expected"; break;
			case 103: s = "??? expected"; break;
			case 104: s = "invalid ClassMemberDecl"; break;
			case 105: s = "invalid FunctionDecl"; break;
			case 106: s = "invalid MethodDecl"; break;
			case 107: s = "invalid MethodDecl"; break;
			case 108: s = "invalid Expression"; break;
			case 109: s = "invalid TypeAndToken"; break;
			case 110: s = "invalid MethodSpec"; break;
			case 111: s = "invalid MethodSpec"; break;
			case 112: s = "invalid ReferenceType"; break;
			case 113: s = "invalid FunctionSpec"; break;
			case 114: s = "invalid FunctionBody"; break;
			case 115: s = "invalid PossiblyWildFrameExpression"; break;
			case 116: s = "invalid PossiblyWildExpression"; break;
			case 117: s = "invalid Stmt"; break;
			case 118: s = "invalid OneStmt"; break;
			case 119: s = "invalid IfStmt"; break;
			case 120: s = "invalid ForeachStmt"; break;
			case 121: s = "invalid AssignRhs"; break;
			case 122: s = "invalid SelectExpression"; break;
			case 123: s = "invalid Guard"; break;
			case 124: s = "invalid CallStmtSubExpr"; break;
			case 125: s = "invalid AttributeArg"; break;
			case 126: s = "invalid EquivOp"; break;
			case 127: s = "invalid ImpliesOp"; break;
			case 128: s = "invalid AndOp"; break;
			case 129: s = "invalid OrOp"; break;
			case 130: s = "invalid RelOp"; break;
			case 131: s = "invalid AddOp"; break;
			case 132: s = "invalid UnaryExpression"; break;
			case 133: s = "invalid MulOp"; break;
			case 134: s = "invalid NegOp"; break;
			case 135: s = "invalid ConstAtomExpression"; break;
			case 136: s = "invalid ObjectExpression"; break;
			case 137: s = "invalid ObjectExpression"; break;
			case 138: s = "invalid SelectOrCallSuffix"; break;
			case 139: s = "invalid SelectOrCallSuffix"; break;
			case 140: s = "invalid QuantifierGuts"; break;
			case 141: s = "invalid Forall"; break;
			case 142: s = "invalid Exists"; break;
			case 143: s = "invalid AttributeOrTrigger"; break;
			case 144: s = "invalid QSep"; break;

			default: s = "error " + n; break;
		}
		//errorStream.WriteLine(errMsgFormat, line, col, s);
		errorStream.WriteLine(s);
		count++;
	}

	public void SemErr (int line, int col, string! s) {
		errorStream.WriteLine(errMsgFormat, line, col, s);
		count++;
	}

	public void SemErr (string filename, int line, int col, string! s) {
		errorStream.WriteLine(errMsgFormat4, filename, line, col, s);
		count++;
	}
	
	public void SemErr (string s) {
		errorStream.WriteLine(s);
		count++;
	}

    public void SemErr(IToken! tok, string! msg) {  // semantic errors
      SemErr(tok.filename, tok.line, tok.col, msg);
    }
	
	public void Warning (int line, int col, string s) {
		errorStream.WriteLine(errMsgFormat, line, col, s);
	}
	
	public void Warning(string s) {
		errorStream.WriteLine(s);
	}
} // Errors


public class FatalError: Exception {
	public FatalError(string m): base(m) {}
}

}