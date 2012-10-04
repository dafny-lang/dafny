" Vim syntax file
" Language: Dafny
" Author: Kuat Yessenov
" Date: 6/24/2010

syntax clear
syntax case match
syntax keyword dafnyFunction function predicate copredicate method constructor
syntax keyword dafnyTypeDef class datatype codatatype type iterator
syntax keyword module import opened as default
syntax keyword dafnyConditional if then else match case 
syntax keyword dafnyRepeat while parallel
syntax keyword dafnyStatement assume assert return yield new print break label where calc
syntax keyword dafnyKeyword var ghost returns yields null static this refines
syntax keyword dafnyType bool nat int seq set multiset object array array2 array3 map
syntax keyword dafnyLogic requires ensures modifies reads decreases invariant 
syntax keyword dafnyOperator forall exists old fresh choose
syntax keyword dafnyBoolean true false
  
syntax region dafnyString start=/"/ skip=/\\"/ end=/"/

syntax match dafnyComment /\/\/.*/
syntax region dafnyComment start="/\*" end="\*/"

syntax match dafnyNumber /\d\+\>/
syntax match dafnyIdentifier /\<\w\+\>/

syntax match dafnyOperator "==>"
syntax match dafnyOperator "<==>"
syntax match dafnyOperator "::"

highlight link dafnyFunction Function
highlight link dafnyTypeDef Typedef
highlight link dafnyConditional Conditional
highlight link dafnyRepeat Repeat
highlight link dafnyKeyword Keyword
highlight link dafnyType Type
highlight link dafnyLogic Debug
highlight link dafnyComment Comment
highlight link dafnyString String
highlight link dafnyNumber Number
highlight link dafnyOperator Operator
highlight link dafnyStatement Statement
highlight link dafnyBoolean Boolean 
