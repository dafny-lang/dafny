---
title: It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.
---

## Question

It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.

## Answer

The desired output is present in all current Dafny backends. But note that
if the print statement does not include the `\n`, then the output may not either.
In that case the output may be (depending on the shell you are using)
concatenated with the prompt for the next user input.

For example,
```dafny
method Main() {
  print "Hi";
}
```
produces (with a bash shell)
```
mydafny $ dafny run --target=cs Newline.dfy 

Dafny program verifier finished with 0 verified, 0 errors
Himydafny $
```
