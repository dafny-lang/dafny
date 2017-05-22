" Vim syntax file
" Language: Dafny
" Author: Kuat Yessenov
" Date: 6/24/2010

syntax clear
syntax case match
syntax keyword dafnyFunction function predicate copredicate
syntax keyword dafnyMethod method lemma constructor colemma
syntax keyword dafnyTypeDef class datatype codatatype newtype type iterator trait extends export
syntax keyword dafnyModule abstract module import opened as default
syntax keyword dafnyConditional if then else match case
syntax keyword dafnyRepeat while
syntax keyword dafnyStatement assume assert by return yield new print break label where calc modify
syntax keyword dafnyKeyword var ghost returns yields null static protected this refines include
syntax keyword dafnyType bool char nat int real set iset multiset seq string map imap object array array2 array3
syntax keyword dafnyLogic requires ensures modifies reads decreases invariant witness provides reveals
syntax keyword dafnyOperator forall exists old fresh
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
highlight link dafnyMethod Statement
highlight link dafnyModule StorageClass
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
