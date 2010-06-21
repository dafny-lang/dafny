" Vim syntax file
" Language: Dafny
" Author: Kuat Yessenov (6/7/2010)

syntax clear
syntax case match
syntax keyword dafnyFunction function method
syntax keyword dafnyTypeDef class datatype 
syntax keyword dafnyConditional if then else match case 
syntax keyword dafnyRepeat for while
syntax keyword dafnyKeyword var ghost assert returns null return call static
syntax keyword dafnyType int bool seq set
syntax keyword dafnyLogic requires ensures modifies reads decreases invariant 
syntax keyword dafnyOperator forall exists old
  
syntax region dafnyString start=/"/ skip=/\\"/ end=/"/

syntax match dafnyComment /\/\/.*/

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
highlight link dafnyOperator Operator
