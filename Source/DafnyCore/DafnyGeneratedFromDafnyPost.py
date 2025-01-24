import re
import os
import sys
# Define output as the first command-line argument
output = sys.argv[1]

# We will remove all the namespaces Std.* except Std.Wrappers
# Also, we will replace every Dafny.HaltException("Backends\\Rust\\ by Dafny.HaltException("Backends/Rust/
# to ensure the source is built the same on linux
# It requires 16 backslashes for escaping because
# - 2 as there are two backslashes
# - 2 as it's a bash string
# - 2 as it's a python string
# - 2 as it's an escaped backslash
# Last step is to split the generated file by namespace and put each in a separate directory inside Generated/
# according to the namespace. It will make formatting easier.

# test if the file exists before opening it. If not, fail gracefully
if not os.path.exists(output + '.cs'):
  print(f"File {output}.cs was not generated. Fix issues and re-run ./DafnyGeneratedFromDafny.sh")
  exit()

if os.path.exists(output + '-cs.dtr'):
    os.remove(output + '-cs.dtr')
    print("File deleted: " + output + '-cs.dtr')

with open(output + '.cs', 'r' ) as f:
  content = f.read()
  content_trimmed = re.sub('\[assembly[\s\S]*?(?=namespace Formatting)|namespace\s+\w+\s*\{\s*\}\s*//.*', '', content, flags = re.M)
  content_new = re.sub('\r?\nnamespace\s+(Std\.(?!Wrappers)(?!Strings)(?!Collections.Seq)(?!Arithmetic)(?!Math)\S+)\s*\{[\s\S]*?\}\s*// end of namespace \\1', '', content_trimmed, flags = re.M)
  content_new = re.sub('Backends\\\\\\\\Rust\\\\\\\\', 'Backends/Rust/', content_new, flags = re.M)

  # Any test looking like "  if()"

  test_output = "../DafnyCore.Test/"

  if not os.path.exists(output):
    os.makedirs(output)
  
  if not os.path.exists(test_output+output):
    os.makedirs(test_output+output)

  prelude_match = re.match(r'(.*?)\nnamespace', content_new, re.DOTALL)
  prelude = prelude_match.group(1).strip() if prelude_match else ""
  prelude = (prelude +
    "\n#pragma warning disable CS0164 // This label has not been referenced" +
    "\n#pragma warning disable CS0162 // Unreachable code detected" +
    "\n#pragma warning disable CS1717 // Assignment made to same variable")

  # Define a regular expression to match the prelude and namespace blocks
  pattern = re.compile(r'(namespace\s+([\w.]+)\s*{[\s\S]*?}\s*//\s*end\s*of\s*namespace\s+\2)')
  # Find the prelude and namespace blocks
  matches = pattern.findall(content_new)

  # Iterate over matches and create files for each namespace
  for match in matches:
    namespace_content = match[0]  # Entire namespace block
    namespace_name = match[1]
    file_content = f"{prelude}\n\n{namespace_content}"

    # If the name of the namespace ends with "coverage", we move this test
    # to ../DafnyCore.Test/{output}/....
    file_path_prefix = ""
    if namespace_name.endswith("Coverage") or namespace_name.endswith("Test"):
      file_path_prefix = test_output
    
    # Write content to a file
    file_path = f"{file_path_prefix}{output}/{namespace_name.replace('.', '_')}.cs"  # Replace dots with underscores in file name
    with open(file_path, 'w') as file:
      file.write(file_content)

    print(f"File generated: {file_path}")

  # Special-case the FuncExtensions class, which isn't declared inside a namespace
  func_extensions_pattern = re.compile(r'(internal\s+static\s+class\s+FuncExtensions\s*{[\s\S]*?}\s*//\s*end\s*of\s*class\s*FuncExtensions)')
  match = func_extensions_pattern.search(content)
  func_extensions_content = match[0]

  file_content = f"{prelude}\n\n{func_extensions_content}"
  file_path = f"{output}/FuncExtensions.cs"
  with open(file_path, 'w') as file:
    file.write(file_content)

  print(f"File generated: {file_path}")

# Now delete the file output.cs
os.remove(output + '.cs')
print("File deleted: " + output + '.cs')
