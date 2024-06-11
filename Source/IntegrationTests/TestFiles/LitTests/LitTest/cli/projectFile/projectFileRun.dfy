// NONUNIFORM: we're not testing the execution behavior
// Run works with project files
// RUN: %baredafny run --show-snippets:false --build=Build/temp --warn-shadowing=false --use-basename-for-filename "%S/dfyconfig.toml" > "%t"

// RUN: %diff "%s.expect" "%t"
