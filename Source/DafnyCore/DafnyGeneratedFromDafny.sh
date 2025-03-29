#! /usr/bin/env bash
# Until we get proper dependency to previous Dafny, you have to generate the file GeneratedFromDafny.cs
# To remove this manual build process, when it will be appropriate:
# 1. Delete the file GeneratedFromDafny.cs
# 2. Add a dependency to 
#      <PackageReference Include="dafny.msbuild" Version="1.0.0" />
# That's it! The same file will now be automatically generated as obj/Debug/net8.0/GeneratedFromDafny.cs
# 3. Remove the following dependencies that are being taken care by dafny-msbuild
#       <PackageReference Include="Microsoft.Build.Framework" Version="16.5.0" PrivateAssets="All" />
#       <PackageReference Include="Microsoft.Build.Utilities.Core" Version="16.5.0" PrivateAssets="All" />
#       <PackageReference Include="System.Linq.Parallel" Version="4.3.0" PrivateAssets="All" />

# If the argument --no-verify is passed to the script, we pop it and will pass it to the dafny command below
if [ "$#" != 0 ] && [ "$1" == "--no-verify" ]; then
  noverify="--no-verify"
  shift
else
  noverify=""
fi
  
# If an argument is passed to the script, store it in this variable. Otherwise use the default "GeneratedFromDafny.cs"
# Something like output = if no arguments then  "GeneratedFromDafny.cs" else first argument

if [ "$#" != 0 ]; then
  output="$1"
else
  output="GeneratedFromDafny"
fi

../../Scripts/dafny translate cs dfyconfig.toml --output $output.cs $noverify
# Exit with error code if the previous command fails
if [ $? -ne 0 ]; then
  exit 1
fi

python3 DafnyGeneratedFromDafnyPost.py $output
