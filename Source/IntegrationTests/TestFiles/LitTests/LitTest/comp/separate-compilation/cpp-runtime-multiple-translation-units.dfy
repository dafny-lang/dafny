// NONUNIFORM: This exercises the C++ runtime header's native linkage without invoking the Dafny compiler.
// Both translation units include the runtime; header-defined functions must not produce duplicate symbols.
// RUN: g++ -std=c++17 -I "%binaryDir/DafnyRuntimeCpp" "%S/Inputs/cpp-runtime-linkage/producer.cpp" "%S/Inputs/cpp-runtime-linkage/main.cpp" -o "%t.exe"
// RUN: "%t.exe" > "%t"
// RUN: %diff "%s.expect" "%t"
