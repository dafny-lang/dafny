// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Mod1 
{
	type IntRenamed = int
} 

import opened Mod1