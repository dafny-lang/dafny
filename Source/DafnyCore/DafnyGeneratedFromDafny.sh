#! /usr/bin/env bash
# Until we get proper dependency to previous Dafny, you have to generate the file GeneratedFromDafny.cs
# To remove this manual build process, when it will be appropriate:
# 1. Delete the file GeneratedFromDafny.cs
# 2. Add a dependency to 
#      <PackageReference Include="dafny.msbuild" Version="1.0.0" />
# That's it! The same file will now be automatically generated as obj/Debug/net6.0/GeneratedFromDafny.cs
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

# If the argument --no-format is passed to the script, we pop it and won't format the resulting cs
if [ "$#" != 0 ] && [ "$1" == "--no-format" ]; then
  noformat="true"
  shift
else
  noformat="false"
fi
  
# If an argument is passed to the script, store it in this variable. Otherwise use the default "GeneratedFromDafny.cs"
# Something like output = if no arguments then  "GeneratedFromDafny.cs" else first argument

if [ "$#" != 0 ]; then
  output="$1"
else
  output="GeneratedFromDafny"
fi

../../Scripts/dafny translate cs dfyconfig.toml --output $output.cs $noverify

# We will remove all the namespaces Std.* except Std.Wrappers
python3 -c "
import re
with open ('$output.cs', 'r' ) as f:
  content = f.read()
  content_trimmed = re.sub('\\[assembly[\\s\\S]*?(?=namespace Formatting)|namespace\\s+\\w+\\s*\\{\\s*\\}\\s*//.*|_\\d_', '', content, flags = re.M)
  content_new = re.sub('\\r?\\nnamespace\\s+(Std\\.(?!Wrappers)(?!Strings)(?!Collections.Seq)(?!Arithmetic)(?!Math)\\S+)\\s*\\{[\\s\\S]*?\\}\\s*// end of namespace \\\\1', '', content_trimmed, flags = re.M)

with open('$output.cs', 'w') as w:
  w.write(content_new)
"

if [ "$noformat" == "false" ]; then
  dotnet format whitespace --include $output.cs 
fi