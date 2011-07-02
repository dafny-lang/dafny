namespace Ast

open System
open System.Numerics

type Type =
  | IntType
  | BoolType
  | SetType of Type (* type parameter *)
  | SeqType of Type (* type parameter *)
  | NamedType of string
  | InstantiatedType of string * Type (* type parameter *)

type Const = 
  | IntConst   of int
  | BoolConst  of bool
  | SetConst   of Set<Const option>
  | SeqConst   of (Const option) list
  | NullConst
  | ThisConst  of (* loc id *) string * Type option
  | NewObj     of (* loc id *) string * Type option
  | Unresolved of (* loc id *) string 

type VarDecl =
  | Var of string * Type option

type Expr =
  | IntLiteral of BigInteger
  | IdLiteral of string
  | Star
  | Dot of Expr * string
  | UnaryExpr of string * Expr
  | BinaryExpr of int * string * Expr * Expr
  | SelectExpr of Expr * Expr
  | UpdateExpr of Expr * Expr * Expr
  | SequenceExpr of Expr list
  | SeqLength of Expr
  | ForallExpr of VarDecl list * Expr

type Stmt =
  | Block of Stmt list
  | Assign of Expr * Expr

type Signature =
  | Sig of VarDecl list * VarDecl list

type Member =
  | Field of VarDecl
  | Method of (* name *) string * Signature * (* pre *) Expr * (* post *) Expr * (* isConstructor *) bool
  | Invariant of Expr list

type TopLevelDecl =
  | Class of string * string list * Member list
  | Model of string * string list * VarDecl list * Expr list * Expr
  | Code of string * string list

type SyntacticProgram =
  | SProgram of TopLevelDecl list

type Component =
  | Component of (*class*)TopLevelDecl * (*model*)TopLevelDecl * (*code*)TopLevelDecl

type Program =
  | Program of Component list

