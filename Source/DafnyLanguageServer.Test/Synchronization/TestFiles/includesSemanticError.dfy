include "./semanticError.dfy"
module IncludesSyntaxError {
 import SemanticError
 method Caller() {
   SemanticError.WithSemanticError();
 }
}
