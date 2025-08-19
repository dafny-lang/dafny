#!/bin/env node
// Every comment of this file starting with //# comes from the file ../docs/dev/VERSIONBUMP.md
// and vice-versa

//# After each release, we change the version number by first running
//#     python3 Scripts/prepare_release.py NEXT_VERSION set-next-version
//# where NEXT_VERSION is the version of the last release of the format
//# `major.minor.patch` and the patch has been increased by 1. This script
//# has for effect to change the version number in `Source/Directory.Build.props`.
//# Then, many things in Dafny that depend on this version number have to be
//# updated.
//# This file is an exhaustive list of everything that needs to be updated
//# whenever the version number changes. All these steps are
//# executable by running
//#     ./Scripts/bump_version_number.js NEW_VERSION
//# and `make bumpversion-test` run by the CI on each release
//# verifies that this file is in sync with that script.

const fs = require('fs');
const { promisify } = require('util');
const {exec, spawn} = require('child_process');
const execAsync = promisify(exec);
const minutes = 60*1000;
const versionFile = "Source/Directory.Build.props";
// Change the working directory to Dafny
process.chdir(__dirname + "/..");
const prefixLinkedComment = "//# ";
var existingVersion = "";
//# Assuming `<TestDirectory>` to be `Source/IntegrationTests/TestFiles/LitTests/LitTest`,
//# perform the following:
const TestDirectory = "Source/IntegrationTests/TestFiles/LitTests/LitTest";
var {version, testMode} = processArgs(process.argv.slice(2)); // Remove "node" and the script's name.
if(testMode) {
  test();
} else {
  synchronizeRepositoryWithNewVersionNumber();
}

async function synchronizeRepositoryWithNewVersionNumber() {
  existingVersion = await getVersionNumber();
  if(version === false) {
    version = existingVersion;
  } else {
    await bumpVersionNumber(version);
  }
  //# * Update standard library doo files instead of rebuilding to avoid Z3 timeout issues
  const standardLibraryDir = "Source/DafnyStandardLibraries/binaries";
  const standardLibraryDooFiles = fs.readdirSync(standardLibraryDir)
    .filter(file => file.endsWith('.doo'))
    .map(file => `${standardLibraryDir}/${file}`);

  for (const dooFile of standardLibraryDooFiles) {
    await updateDooVersion(dooFile, version);
  }

  // Verify that binaries have been updated.
  await sanityCheckStandardLibraries(version);

  //# * In the test directory `Source/IntegrationTests/TestFiles/LitTests/LitTest`,
  //# * Update test doo files instead of rebuilding
  //#   * Update `pythonmodule/multimodule/PythonModule1.doo` version
  //#   * Update `pythonmodule/nestedmodule/SomeNestedModule.doo` version
  //#   * Update `gomodule/multimodule/test.doo` version
  const testDooFiles = [
    `${TestDirectory}/pythonmodule/multimodule/PythonModule1.doo`,
    `${TestDirectory}/pythonmodule/nestedmodule/SomeNestedModule.doo`,
    `${TestDirectory}/gomodule/multimodule/test.doo`
  ];

  for (const dooFile of testDooFiles) {
    if (fs.existsSync(dooFile)) {
      await updateDooVersion(dooFile, version);
    }
  }

  //#   * Search for `dafny_version = ` in checked-in `.dtr` files of the `<TestDirectory>`
  //#    and update the version number.
  var files = await findFiles(TestDirectory, ".*\\.dtr");
  assert_eq(files.length != 0, true);
  for(let file of files) {
    //#     Except for the file NoGood.dtr which is not valid.
    if(file.endsWith("NoGood.dtr")) {
      continue;
    }
    //#     Except for WrongDafnyVersion.dtr as well. 
    if(file.endsWith("WrongDafnyVersion.dtr")) {
      continue;
    }
    await replaceInFile(/dafny_version = "\d+\.\d+\.\d+/, `dafny_version = "${version}`,
      `${TestDirectory}/${file}`);
  }

  //# * In `Source/DafnyRuntime/DafnyRuntimeJava/build.gradle`, search for `version = ` and update the version number
  await replaceInFile(/version = '(\d+\.\d+\.\d+)/, `version = '${version}`,
    `Source/DafnyRuntime/DafnyRuntimeJava/build.gradle`, existingVersion);
  
  //# * In `Source/DafnyRuntime/DafnyRuntimePython/pyproject.toml`, search for `version = ` and update the version number
  await replaceInFile(/version = "(\d+\.\d+\.\d+)"/, `version = "${version}"`,
    `Source/DafnyRuntime/DafnyRuntimePython/pyproject.toml`, existingVersion);

  //#   * Update `comp/separate-compilation/translation-records/InvalidFormat.dfy.expect` by updating the version number after `by Dafny `
  await replaceInFile(/by Dafny \d+\.\d+\.\d+/, `by Dafny ${version}`,
    `${TestDirectory}/comp/separate-compilation/translation-records/InvalidFormat.dfy.expect`);

  //# * Update the Dafny runtime version number by searching for `DafnyRuntime-` and updating the version right afterwards, in the files `DafnyPipeline.csproj` and `DafnyRuntime.csproj`
  await replaceInFile(/DafnyRuntime-(\d+\.\d+\.\d+)\.jar/, `DafnyRuntime-${version}.jar`,
    `Source/DafnyPipeline/DafnyPipeline.csproj`, existingVersion);
  await replaceInFile(/DafnyRuntime-(\d+\.\d+\.\d+)\.jar/, `DafnyRuntime-${version}.jar`,
    `Source/DafnyRuntime/DafnyRuntime.csproj`, existingVersion);
}

async function updateDooVersion(dooPath, newVersion) {
  const tempDir = `${dooPath}_temp`;
  
  try {
    // Create temp directory
    await execAsync(`mkdir -p "${tempDir}"`);
    
    // Unzip doo file
    await execAsync(`unzip -o "${dooPath}" -d "${tempDir}"`);
    
    // Read manifest.toml
    const manifestPath = `${tempDir}/manifest.toml`;
    let manifestContent = await fs.promises.readFile(manifestPath, 'utf-8');
    
    // Update version
    manifestContent = manifestContent.replace(
      /dafny_version = "(\d+\.\d+\.\d+)\.0"/,
      `dafny_version = "${newVersion}.0"`
    );
    
    // Write updated manifest
    await fs.promises.writeFile(manifestPath, manifestContent);
    
    // Rezip
    const fileName = dooPath.split('/').pop();
    await execAsync(`cd "${tempDir}" && zip -r "../${fileName}_new" *`);
    await execAsync(`mv "${tempDir}/../${fileName}_new" "${dooPath}"`);
    
    console.log(`Updated ${dooPath} to version ${newVersion}`);
  } finally {
    // Cleanup
    await execAsync(`rm -rf "${tempDir}"`).catch(() => {});
  }
}

// Unzips the file Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries.doo (it's actually a zip file)
// Fetch the content of Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries/manifest.toml
// Verify that dafny_version = "Major.Minor.Patch.0" corresponds ot the version that is provided
async function sanityCheckStandardLibraries(version) {
  if(testMode) {
    console.log("Would have run a sanity check");
    return;
  }
  console.log("Sanity-checking standard libraries");
  try {
    await execute("unzip -o Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries.doo -d Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries");
  } catch(e) {
    console.log("Could not unzip Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries.doo", e);
    throw e;
  }
  var manifest = await fs.promises.readFile("Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries/manifest.toml", "utf-8");
  var match = manifest.match(/dafny_version = "(\d+\.\d+\.\d+)/);
  assert_eq(match != null, true, "Could not find dafny_version in manifest.toml");
  assert_eq(match[1], version, `dafny_version in manifest.toml is ${match[1]} but should have been ${version}. Something went wrong`);
  await execute("rm -rf Source/DafnyStandardLibraries/binaries/DafnyStandardLibraries");
}


// Returns the current version number
async function getVersionNumber() {
  var versionFileContent = await fs.promises.readFile(versionFile, "utf-8");
  var version = readVersionNumber(versionFileContent);
  if(version === false) {
    throw "Could not find version number in " + versionFile;
  }
  return version;
}

// Returns the version number from the given file content (see const versionFile)
function readVersionNumber(versionFileContent) {
  var versionMatch = versionFileContent.match(/<VersionPrefix>(\d+\.\d+\.\d+)<\/VersionPrefix>/);
  if(versionMatch != null) {
    return versionMatch[1];
  }
  return false;
}

// Increases the patch of the given version number
async function bumpVersionNumber(version) {
  console.log(`Bumping version number to ${version}`);
  var versionFileContent = await fs.promises.readFile(versionFile, "utf-8");
  newVersionFileContent = replaceVersionNumber(versionFileContent, version);
  if(testMode) {
    if(newVersionFileContent === versionFileContent) {
      throw "Expected to find " + version + " in " + versionFile;
    }
    console.log("Would have updated  " + versionFile + " to " + newVersionFileContent);
    return;
  }
  await fs.promises.writeFile(versionFile, newVersionFileContent);
}

// Replace the given version number in the given file that has the old version number
function replaceVersionNumber(versionFileContent, newVersion) {
  return versionFileContent.replace(/<VersionPrefix>\d+\.\d+\.\d+<\/VersionPrefix>/, `<VersionPrefix>${newVersion}</VersionPrefix>`);
}


// Spawn async
function spawnAsync(commandAndArgs) {
  return new Promise((resolve, reject) => {
    // Regular expression to match quoted arguments and non-quoted parts
    const regex = /'[^']*'|"[^"]*"|\S+/g;
    
    // Extract all matches and clean up quotes
    const parts = commandAndArgs.match(regex).map(part => {
      // Remove surrounding quotes (both single and double) if they exist
      if ((part.startsWith('"') && part.endsWith('"')) || 
          (part.startsWith("'") && part.endsWith("'"))) {
        return part.slice(1, -1);
      }
      return part;
    });

    const command = parts[0];
    const args = parts.slice(1);
    const childProcess = spawn(command, args);

    childProcess.stdout.on('data', (data) => {
      process.stdout.write(`| ${data}`);
    });

    childProcess.stderr.on('data', (data) => {
      process.stdout.write(`! ${data}`);
    });

    childProcess.on('close', (code) => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`Process exited with code ${code}`));
      }
    });
  });
}

// Execute each command in its arguments
async function execute() {
  var commands = arguments;
  for(let i = 0; i < commands.length; i++) {
    let command = commands[i];
    if(testMode) {
      console.log("Would have run " + command);
    } else {
      console.log("Running " + command);
      await spawnAsync(command);
    }
  }
}

// Find files in the given directory, recursively
// Returns them with the relative path from the given directory
async function findFiles(directory, regexString) {
  var files = [];
  var regexFilter = new RegExp(regexString);
  var dir = await fs.promises.opendir(directory);
  for await (const dirent of dir) {
    if(dirent.isDirectory()) {
      var subFiles = await findFiles(directory + "/" + dirent.name, regexString);
      files = files.concat(subFiles.map(f => dirent.name + "/" + f));
    } else if(dirent.isFile() && regexFilter.test(dirent.name)) {
      files.push(dirent.name);
    }
  }
  return files;
}

// Execute the given comment, with the possibility of timing out
function executeWithTimeout(command, timeout) {
  if(testMode) {
    console.log("Would have run " + command + " with a timeout of " + timeout);
    return new Promise((resolve, reject) => { resolve(); });
  }
  // Instead of having an async closure, we are going to return the promise directly
  // so that it can be fullfilled either way.
  return new Promise((resolve, reject) => {
    var finished = false;
    var childProcess = undefined;
    var timeoutId = setTimeout(() => {
      if(!finished) {
        finished = true;
        if(typeof childProcess != undefined) {
          childProcess.kill();
        }
        resolve({ok: false, log: `Timeout after ${timeout/1000}s`});
      }
    }, timeout);
    console.log(`Running ${command} with timeout of ${timeout/1000}s`)
    childProcess = exec(command, (error, stdout, stderr) => {
      clearTimeout(timeoutId);
      finished = true;
      if(error) {
        resolve({ok: false, log: (error + "\n" + stderr + "\n" + stdout).trim()});
      } else {
        resolve({ok: true, log: stdout, answer: undefined});
      }
    });
    // Add these two handlers
    childProcess.stdout.on('data', (data) => {
      process.stdout.write(`| ${data}`);
    });

    childProcess.stderr.on('data', (data) => {
      process.stdout.write(`! ${data}`);
    });
  });
}

// Find the regex in the given file, and replaces it with the given replacement.
async function replaceInFile(regex, replacement, fileName, testExistingVersion = null) {
  var fileContent = await fs.promises.readFile(fileName, 'utf-8');
  // Replace "Dafny \d.\d.\d" by the new version
  var previous = fileContent.match(regex);
  if(previous == null ) {
    throw `Could not find ${regex} in ${fileName}`;
  }
  var newContent = fileContent.replace(regex, replacement);
  if(testMode) {
    if(testExistingVersion != null) {
      assert_eq(previous[1], testExistingVersion);
    }
    console.log(`Would have replaced ${previous[0]} with ${replacement} in ${fileName}`);
    if(newContent == fileContent) {
      throw "Error in replaceInFile, replacement did not do anything";
    }
  } else {
    await fs.promises.writeFile(fileName, newContent);
  }
}

// Process the arguments.
// If the first argument is --test, then we set the test mode where
// we are going to read this file and verify that all lines of ../docs/dev/VERSIONBUMP.md
// became a comment in this file.
function processArgs(args) {
  var testMode, version;
  testMode = args[0] == "--test";
  if (testMode) {
    args = args.slice(1);
  }

  // If another argument is given, it's a version number that we can update 
  // If there is one argument, it must be the new version number.
  var version = false;
  if (args.length > 0) {
    version = args[0];
    if (!version.match(/^\d+\.\d+\.\d+$/)) {
      console.log(`Invalid version number ${version}`);
      process.exit(1);
    }
  }
  return {version, testMode};
}

////////////////// Testing part to ensure this script is in sync /////////////

async function test() {
  await ensureTakesIntoAccountAllReleaseInstructions();
  assert_eq(readVersionNumber(
    "\n   <VersionPrefix>1.2.3</VersionPrefix>\n"), "1.2.3");
  assert_eq(readVersionNumber(
    "  <VersionPrefix>1.2</VersionPrefix>"), false);
  assert_eq(replaceVersionNumber(
    "\n   <VersionPrefix>1.2.3</VersionPrefix>\n", "1.2.4"), 
    "\n   <VersionPrefix>1.2.4</VersionPrefix>\n");
  await synchronizeRepositoryWithNewVersionNumber(); // Test mode
}

// Step to ensure all the public release instructions are taken into account
async function ensureTakesIntoAccountAllReleaseInstructions() {
  if(version === false) {
    version = await getVersionNumber();
  } else {
    await bumpVersionNumber(version);
  }
  // Read this file itself, and ensure every line of docs/dev/RELEASE.md
  // appears somewhere in this file in its own line, possibly trimmed
  var thisScript = await fs.promises.readFile(__filename, 'utf-8');
  var publicBumpFile = 'docs/dev/VERSIONBUMP.md';
  var publicReleaseInstructions = await fs.promises.readFile(publicBumpFile, 'utf-8');
  var lines = publicReleaseInstructions.split("\n");
  var thisScriptLines = thisScript.split("\n").
    map(line => line.trim()).
    filter(line => line.startsWith(prefixLinkedComment)).
    map(line => line.substring(prefixLinkedComment.length).trim());
  var missingLines = [];
  var lineNumber = 1;
  for(let line of lines) {
    trimmedLine = line.trim();
    if(trimmedLine.length > 0 && !trimmedLine.startsWith("#") && thisScriptLines.indexOf(trimmedLine) === -1) {
      missingLines.push("//# " + line);
    }
    lineNumber++;
  }
  if(missingLines.length > 0) {
    for(let line of missingLines) {
      console.log(line);
    }
    console.log(`------------------------------------`);
    console.log(`${missingLines.length} lines of ${publicBumpFile} were not found in ${__filename} ^^`);
    console.log(`Please update either file.`);
    process.exit(1);
  }

  // Now verify that each line of thisScriptLines is in the publicBumpFile
  var extraLines = [];
  var linesTrimmed = lines.map(line => line.trim());
  for(let line of thisScriptLines) {
    if(linesTrimmed.indexOf(line) === -1) {
      extraLines.push(line);
    }
  }
  if(extraLines.length > 0) {
    for(let line of extraLines) {
      console.log(line);
    }
    console.log(`------------------------------------`);
    console.log(`${extraLines.length} comment lines of ${__filename} were not found in ${publicBumpFile} ^^`);
    console.log(`Please update either file.`);
    process.exit(1);
  }
}

function assert_eq(got, expected, msg=undefined) {
  if(got != expected) {
    throw "Expected " + expected + ", got " + got + (msg != undefined ? " - " + msg : "");
  }
}