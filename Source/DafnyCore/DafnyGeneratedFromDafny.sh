#! /bin/bash
# Until we get proper dependency to previous Dafny, you have to generate the file GeneratedFromDafny.cs
# To remove this manual build process, when it will be appropriate:
# 1. Delete the file GeneratedFromDafny.cs
# 2. Add a dependcy to 
#      <PackageReference Include="dafny.msbuild" Version="1.0.0" />
# That's it! The same file will now be automatically generated as obj/Debug/net6.0/GeneratedFromDafny.cs
# 3. Depending if we added them, we might have to remove the following dependencies that are being taken care by dafny-msbuild
#       <PackageReference Include="Microsoft.Build.Framework" Version="16.5.0" PrivateAssets="All" />
#       <PackageReference Include="Microsoft.Build.Utilities.Core" Version="16.5.0" PrivateAssets="All" />
#       <PackageReference Include="System.Linq.Parallel" Version="4.3.0" PrivateAssets="All" />
../../Binaries/Dafny.exe translate cs --output GeneratedFromDafny.cs AST/Formatting.dfy
python -c "
import re
with open ('GeneratedFromDafny.cs', 'r' ) as f:
  content = f.read()
  content_new = re.sub('\\[assembly[\\s\\S]*?(?=namespace Formatting)|namespace\\s+\\w+\\s*\\{\\s*\\}\\s*//.*|_\\d_', '', content, flags = re.M)
with open('GeneratedFromDafny.cs', 'w') as w:
  w.write(content_new)
"
dotnet tool run dotnet-format -w --include GeneratedFromDafny.cs