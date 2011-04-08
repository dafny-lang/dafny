namespace Ast
open System
open System.Numerics


type Type =
  | NamedType of string
  | InstantiatedType of string * Type

type VarDecl =
  | Var of string * Type option

type Expr =
  | IntLiteral of BigInteger
  | IdLiteral of string
  | Star
  | Dot of Expr * string
  | UnaryExpr of string * Expr
  | BinaryExpr of (int * string) * Expr * Expr
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
  | Constructor of string * Signature * Expr * Stmt list
  | Method of string * Signature * Expr * Stmt list

type TopLevelDecl =
  | Class of string * string list * Member list
  | Model of string * string list * VarDecl list * Expr list * Expr
  | Code of string * string list

type Program =
  | Program of TopLevelDecl list
