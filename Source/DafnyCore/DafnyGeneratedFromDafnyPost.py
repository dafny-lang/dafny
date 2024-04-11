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
with open (output + '.cs', 'r' ) as f:
  content = f.read()
  content_trimmed = re.sub('\[assembly[\s\S]*?(?=namespace Formatting)|namespace\s+\w+\s*\{\s*\}\s*//.*|_\d_', '', content, flags = re.M)
  content_new = re.sub('\r?\nnamespace\s+(Std\.(?!Wrappers)(?!Strings)(?!Collections.Seq)(?!Arithmetic)(?!Math)\S+)\s*\{[\s\S]*?\}\s*// end of namespace \\1', '', content_trimmed, flags = re.M)
  content_new = re.sub('Backends\\\\\\\\Rust\\\\\\\\', 'Backends/Rust/', content_new, flags = re.M)

  if not os.path.exists(output):
    os.makedirs(output)

  prelude_match = re.match(r'(.*?)\nnamespace', content_new, re.DOTALL)
  prelude = prelude_match.group(1).strip() if prelude_match else ""

  # Define a regular expression to match the prelude and namespace blocks
  pattern = re.compile(r'(namespace\s+([\w.]+)\s*{[\s\S]*?}\s*//\s*end\s*of\s*namespace\s+\2)')
  # Find the prelude and namespace blocks
  matches = pattern.findall(content_new)

  # Iterate over matches and create files for each namespace
  for match in matches:
    namespace_content = match[0]  # Entire namespace block
    namespace_name = match[1]
    file_content = f"{prelude}\n\n{namespace_content}"

    # Write content to a file
    file_path = f"{output}/{namespace_name.replace('.', '_')}.cs"  # Replace dots with underscores in file name
    with open(file_path, 'w') as file:
      file.write(file_content)

    print(f"File generated: {file_path}")

# Now delete the file output.cs
os.remove(output + '.cs')
print("File deleted: " + output + '.cs')