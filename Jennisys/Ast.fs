//  ####################################################################
///   The AST of a Jennisy program
///
///   author: Rustan Leino (leino@microsoft.com)
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

namespace Ast

open System
open System.Numerics

type Type =
  | IntType
  | BoolType
  | SetType of Type (* type parameter *)
  | SeqType of Type (* type parameter *)
  | NamedType of string * string list (* type parameters *)  
  | InstantiatedType of string * Type list (* type parameters *)

type VarDecl =
  | Var of string * Type option

type Expr =
  | IntLiteral of int
  | BoolLiteral of bool
  | IdLiteral of string
  | Star
  | Dot of Expr * string
  | UnaryExpr of string * Expr
  | BinaryExpr of int * string * Expr * Expr
  | IteExpr of (* cond *) Expr * (* thenExpr *) Expr * (* elseExpr *) Expr
  | SelectExpr of Expr * Expr
  | UpdateExpr of Expr * Expr * Expr
  | SequenceExpr of Expr list
  | SeqLength of Expr
  | SetExpr of Expr list
  | ForallExpr of VarDecl list * Expr

type Stmt =
  | Block of Stmt list
  | Assign of Expr * Expr

type Signature =
  | Sig of (* ins *) VarDecl list * (* outs *) VarDecl list

type Member =
  | Field of VarDecl
  | Method of (* name *) string * Signature * (* pre *) Expr * (* post *) Expr * (* isConstructor *) bool
  | Invariant of Expr list

type TopLevelDecl =
  | Class of string * string list * Member list
  | Model of string * string list * VarDecl list * (* frame *) Expr list * (* invariant *) Expr
  | Code of string * string list

type SyntacticProgram =
  | SProgram of TopLevelDecl list

type Component =
  | Component of (*class*)TopLevelDecl * (*model*)TopLevelDecl * (*code*)TopLevelDecl

type Program =
  | Program of Component list

type Const = 
  | IntConst   of int
  | BoolConst  of bool
  | SetConst   of Set<Const>
  | SeqConst   of Const list
  | NullConst
  | NoneConst
  | ThisConst  of (* loc id *) string * Type option
  | NewObj     of (* loc id *) string * Type option
  | ExprConst  of Expr
  | Unresolved of (* loc id *) string 