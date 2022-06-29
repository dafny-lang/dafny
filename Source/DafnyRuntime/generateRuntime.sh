../../Scripts/dafny /compile:0 /useRuntimeLib /spillTargetCode:3 /compileTarget:java /out:out dafnyRuntime.dfy
find . -type f -name *.java -print0 | xargs -0 sed -i "s/package (\w*)_Compile/$1/"
mv out-java/dafny_Compile DafnyRuntimeJava/src/main/java/dafny/