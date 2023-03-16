#!/usr/bin/env node

/*
 * This file makes it possible to fix an error in Dafny in no time.
 * Add the following alias in your bash profile:
 * 
 *     alias fix='node scripts/fix-dafny-issue.js'
 * 
 * First usage
 * 
 *     > fix [<issueNumber> [<issueKeyword>]]
 * 
 * This script will automate for you and ask questions as appropriate.
 * - It asks you for the issue number and issue keyword if not provided
 * - It fetches the reproducing code of the issue
 * - It adds the test to the codebase
 *   - If it's a CI test, it creates `Test/git-issues/git-issue-<issueNumber>.dfy`
 *     and `Test/git-issues/git-issue-<issueNumber>.dfy.expect`
 *     ensuring it contains a header that LIT can parse, considering the possibility that it needs to be run
 *     Then, it opens these two files in their default editor.
 *   - If it's a language server tests, it adds the code as a first test to
 *     `DafnyLanguageServer.Text/Synchronization/DiagnosticsTest.cs` and 
 *     creates commented placeholders for the interaction and expected results.
 * - It creates a branch named `fix-<issueNumber>-<issueKeyword>`, and commits the files there immediately
 * - It provides you with information to debug the issue in Rider, in CLI dotnet, or just run Dafny.
 * 
 * For an issue that already exists, then you enter the command `fix` alone,
 * - It compiles and runs the tests (CI or Language Server, or both)
 * - If all the tests pass, it asks you if you want to commit the changes.
 *   If you accept:
 * - It creates the `doc/dev/news/<issueNumber>.fix` file for you the first time, asking you about its content
 * - It adds all new and modified files
 *   (including other `git-issue-<issueNumber><suffix>.dfy` files)
 * - It pushes the changes
 * - If the first time it's pushed, it opens your browser with a page
 *   to create the PR with the title and description already populated.
 * 
 * If you want to switch to another issue that you already initiated,
 * ensure the working directory is clean, and run
 * 
 *     > fix <existing issue number | pr number | keyword>
 * 
 * That will make the script to work:
 * - It finds and checks out the branch matching the issue number, the PR number, or a keyword
 * - It opens the test files in their respective editors (for CI tests only)
 * - It rebuilds the solution
 * - It provides you with information on how to test the issue.
 * 
 * If you are already in the issue branch and you want to re-open
 * the test files (because you closed them...), just write 
 * 
 *     > fix open
 * 
 * If you want to do the publishing without running the tests, just write
 * 
 *     > fix force
 * 
 * If you want to add a new or existing test case for the same issue
 * (e.g. Test/git-issues/git-issue-<issueNumber>b.dfy), run
 * 
 *     > fix more <optional existing issue # or existing test name>
 * 
 * If you just write `fix more`, you will be prompted for the argument.
 * - Providing a number will let you import another GitHub issue.
 * - Providing an existing integration test name pattern will ensure that all these
 *   selected tests are run when you run `fix` without arguments.
 *   If more than one test is found, you'll be prompted to confirm your choices.
 */

if(process.cwd().endsWith("scripts")) {
  process.chdir("..");
}

const ABORTED = "ABORTED";
const ACCEPT_HINT = "(ENTER or y for yes, n for no, CTRL+C to abort)\n> ";
const { exit } = require('process');
const readline = require('readline');
const root = require('child_process').execSync('npm root -g').toString().trim();
const fs = require('fs');
let fetch = null;
try {
  fetch = require(root + '/cross-fetch');
} catch(e) {
  console.log("cross-fetch must be installed globally. Run `npm install -g cross-fetch`");
  exit(1);
}
let open = null;
try {
  open = require(root + '/open')
} catch(e) {
  console.log("open must be installed globally. Run `npm install -g open`");
  exit(1);
}
const { promisify } = require('util');
const exec = require('child_process').exec;
const execAsync = promisify(exec);
async function execLog(cmd, hint, returnAbortedIfFailure=true) {
  if(hint) {
    console.log(hint);
  }
  var output = "";
  try {
    output = await execAsync(cmd);
  } catch(e) {
    if(returnAbortedIfFailure) {
      console.log(e);
      return ABORTED;
    } else {
      return e;
    }
  }
  return output;
}

const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout
});
function close() {
  rl.close();
  return false;
}
// Ask the given question and returns the answer of the user
const question = function(input) {
  return new Promise((resolve, reject) => {
    rl.question(input, resolve);
  });
}

// Returns true iff there is no pending changes on the current branch
async function ensureWorkingDirectoryClean() {
  var unstagedChanges = (await execAsync("git diff")).stdout.trim() + (await execAsync("git diff --cached")).stdout.trim();
  if(unstagedChanges != "") {
    return false;//console.log("Please commit your changes before launching this script.");
  }
  return true;
}


// Returns true if the answer can be interpreted as a "yes"
function ok(answer) {
  return answer.toLowerCase() == "y" || answer == "";
}
// Same as question(), but only accepts the answers in the array acceptableAnswers
async function filterQuestion(prompt, acceptableAnswers) {
  var answer = await question(prompt);
  if(acceptableAnswers.indexOf(answer) == -1) {
    console.log("Invalid answer. Please try again.");
    return filter(prompt, acceptableAnswers);
  }
  return answer;
}
// Returns the name of the current branch
async function getCurrentBranch() {
  return (await execAsync("git branch --show-current")).stdout.trim();
}
// If we are on "master", ensures the working directory is clean and pull the latest master
// If we are on a branch,
// - If it's a fix branch, returns the parsed issue number and keyword
// - If it's not a fix branch, try to check out master
async function ensureMasterOrFollowupFix(providedIssueNumber, addOneTestCase) {
  var cleanDirectory = await ensureWorkingDirectoryClean();
  var currentBranch = await getCurrentBranch();
  if(currentBranch != "master") {
    // If the branch is named fix-XXXX-YYYY, then we extract the issue and keyword and we return them
    var match = currentBranch.match(/^fix-(\d+)-(.+)$/);
    var currentBranchMatchesProvidedIssueNumber = addOneTestCase || (match && (providedIssueNumber == null || currentBranch.match(new RegExp(`^fix-.*${providedIssueNumber}.*\$`))));
    if(currentBranchMatchesProvidedIssueNumber) {
      console.log("You are currently on branch " + currentBranch + " which is a fix branch for issue " + match[1] + " and keyword " + match[2]);
      return {issueNumber: match[1], issueKeyword: match[2], cleanDirectory, neededToSwitchToExistingBranch: false};
    }
  }
  if(!cleanDirectory) {
    console.log("Please commit your changes before launching this script.");
    throw ABORTED;
  }
  if(providedIssueNumber != null) {
    // Check if there is an existing fix branch that starts with providedIssueNumber
    var branches = (await execAsync("git branch")).stdout.trim().split("\n").map(b => b.trim());
    var existingFixBranches = branches.filter(b => b.match(new RegExp(`^fix-.*${providedIssueNumber}.*\$`)));
    if(existingFixBranch != null && existingFixBranch.length > 1) {
      console.log("There are multiple fix branches for issue '" + providedIssueNumber + "', please be more specific:\n" + existingFixBranches.join("\n"));
      throw ABORTED;
    }
    if(existingFixBranches != null && existingFixBranches.length == 1) {
      var existingFixBranch = existingFixBranches[0];
      await execLog("git checkout " + existingFixBranch, "Switching to branch " + existingFixBranch);
      // pull the latest changes, if any
      await execLog("git pull", "Pulling the latest changes...", false);
      var m = existingFixBranch.match(new RegExp("^fix-(\\d+)-(.+)$"));
      var issueNumber = m[1];
      var issueKeyword = m[2];
      return {issueNumber, issueKeyword, cleanDirectory, neededToSwitchToExistingBranch: true};
    }
    // Maybe we gave a PR number. We can retrieve the PR and the issue number.
    var js = await getOriginalDafnyIssue(providedIssueNumber);
    if("body" in js && (match = /This PR fixes #(\d+)/.exec(js.body))) {
      console.log("The PR "+providedIssueNumber+" is fixing issue " +match[1] + ". Redirecting...");
      return ensureMasterOrFollowupFix(match[1]);
    }
  }
  if(currentBranch != "master") {
    console.log(`You need to be on the 'master' branch to create ${providedIssueNumber ? "a fix for #" + providedIssueNumber: "a fix."}`);
    if(!ok(await question(`Switch from '${currentBranch}' to 'master'? ${ACCEPT_HINT}`))) {
      console.log("Fixing script aborted.");
      throw ABORTED;
    }
    console.log("switched to master branch");
    console.log((await execAsync("git checkout master")).stdout);
    currentBranch = await getCurrentBranch();
    if(currentBranch != "master") {
      console.log("Failed to checkout master");
      throw ABORTED;
    }
  }
  await execAsync("git pull");
  console.log("Latest master checked out and pulled from origin.")
}

let cache = {};
// Pull the JSON of the given issue number
async function getOriginalDafnyIssue(issueNumber) {
  if(!issueNumber.match(/^\d+$/)) {
    console.log(`Not an issue number: ${issueNumber}`);
    return {};
  }
  if(issueNumber in cache) {
    return cache[issueNumber];
  }
  console.log("Fetching original dafny issue #" + issueNumber);
  var js = await (await fetch("https://api.github.com/repos/dafny-lang/dafny/issues/" + issueNumber)).json();
  cache[issueNumber] = js;
  return js;
}

// Skips the words "open", "force" and "more" from the arguments,
// sets the flags appropriatedly and returns the remaining of the arguments.
function processArgs() {
  var args = [...process.argv];
  var openFiles = false;
  var skipVerification = false;
  var addOneTestCase = false;
  while(args[2] in {"open": 0, "force": 0, "more": 0}) {
    if(args[2] == "open") {
      args.splice(2, 1);
      openFiles = true;
    } else if(args[2] == "force") {
      args.splice(2, 1);
      skipVerification = true;
    } else {
      args.splice(2, 1);
      addOneTestCase = true;
    }
  }
  return {args, openFiles, skipVerification, addOneTestCase};
}

// Given the arguments, returns the issue number and the issue keyword.
async function getIssueNumberAndKeyword(existingBranch, providedIssueNumber, providedKeywordNumber) {
  var neededToSwitchToExistingBranch;
  var fixBranchDidExist = false;
  var issueNumber = "";
  if(existingBranch != undefined) {
    var {issueNumber, issueKeyword, neededToSwitchToExistingBranch} = existingBranch;
    fixBranchDidExist = true;
  } else {
    var issueNumber = providedIssueNumber ?? await question("What is the git issue number? ");
    var issueKeyword = providedKeywordNumber;
    if(issueKeyword == null || issueKeyword == "") {
      console.log("Getting issue keyword...");
      issueKeyword = await getIssueKeyword(issueNumber);
    }
    if(issueKeyword != null && issueKeyword != "") {
      console.log("The suggested issue keyword is the following:\n"+issueKeyword);
    }
    var answer = " ";
    while(!answer.match(/^[-a-zA-Z0-9_]*$/)) {
      answer = await question(
        issueKeyword != null && issueKeyword != "" ?
        "Press ENTER to accept it or write your own keyword (without space):\n> "
        : "Write a keyword for this issue like this and press ENTER (e.g. crash-dafny-resolver):\n> ");
      
    }
    if(answer != "" && answer != " ") {
      issueKeyword = answer;
    }
    if(issueKeyword == null || issueKeyword == "" || !issueKeyword.match(/^[-a-zA-Z0-9_]*$/)) {
      console.log("Did not obtain a suitable issue keyword");
      throw ABORTED;
    }
    neededToSwitchToExistingBranch = false;
  }
  return {issueNumber, issueKeyword, neededToSwitchToExistingBranch, fixBranchDidExist};
}

// Returns the issue keyword from the issue number
async function getIssueKeyword(issueNumber) {
  var js = await getOriginalDafnyIssue(issueNumber);

  // Get the body field of the first post
  var issueKeyword = "title" in js ?
    js.title.toLowerCase().replace(/\b(a|the|fix|in|where|about)( |$)/g, "")
    .replace(/[^a-zA-Z0-9]/g, "-") : "";
  while(issueKeyword.indexOf("-") >= 0 && issueKeyword.length > 50) {
    issueKeyword = issueKeyword.replace(/-[^-]*$/, "");
  }
  if(issueKeyword.length > 50) {
    issueKeyword = issueKeyword.substring(0, 50);
  }
  return issueKeyword;
}

// Create the tests fore the given issue number
async function interactivelyCreateTestFileContent(issueNumber = null, commandLineContent = null) {
  // Retrieve the content of the first post from the issue
  var js = issueNumber != null && issueNumber != "" ? await getOriginalDafnyIssue(issueNumber) : {};
  var isLanguageServer = "labels" in js && js.labels.find(label => 
    label.name.indexOf("language server") >= 0);
  // Get the body field of the first post
  var issueContent = "body" in js ? js.body : "";
  // extract the code contained between ```dafny and ```
  var match = issueContent.match(/```(?:.*dafny)?\r?\n([\s\S]+?)\r?\n```/);
  var programReproducingError = match != null ? match[1] : "";
  var hasMain = programReproducingError.match(/method\s+Main\s*\(/);

  var type = await(question(`Do you want to reproduce this problem\n- On the command line (${isLanguageServer ? "" : "ENTER or "}1)\n- A diagnostic test on the language server(${isLanguageServer ? "ENTER or " : ""}2)\n- A gutter icons test on the language server (3)\n- Don't create test files(4)?\n> `));
  var languageServerDiagnostic = (isLanguageServer && type == "") || type == "2";
  var languageServerIcons = type == "3";
  var skipTestCreation = type == "4";
  if(skipTestCreation) {
    return {programReproducingError, languageServerDiagnostic, skipTestCreation};
  }
  var shouldCompile = !languageServerDiagnostic && !languageServerIcons && ok(await question("Will the test need to be compiled? "+ACCEPT_HINT));
  var shouldRun = shouldCompile && (hasMain || ok(await question("Will the test need to be run (i.e. will have a Main() method)? "+ACCEPT_HINT)));
  var shouldCompileBackend = shouldCompile ? await filterQuestion("Which back-end should be used? cs (default), js, java, go, cpp, py or all? ", ["", "cs", "js", "java", "go", "cpp", "py", "all"]) : "";

  programReproducingError = programReproducingError == "" ? (commandLineContent ?? (shouldRun ? "method Main() {\n  \n}" : "")) : programReproducingError;
  if(languageServerDiagnostic || languageServerIcons) {
    return {programReproducingError, languageServerDiagnostic, languageServerIcons, skipTestCreation};
  }
  var header = "";
  var programArguments = "";
  if(shouldCompile) {
    if(shouldCompileBackend == "") {
      shouldCompileBackend = "cs";
    }
    var c = shouldRun ? "build" : "run";
    if(shouldCompileBackend == "all") {
      header += `// RUN: %baredafny verify %args "%s" > "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:cs "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:js "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:cpp "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:java "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:go "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:py "%s" >> "%t"\n`;
      programArguments = `${c} -t:cs`;
    } else {
      programArguments = `${c} %args -t:${shouldCompileBackend}`;
      header += `// RUN: %baredafny ${programArguments} "%s" > "%t"\n`;
    }
  } else {
    var shouldVerify = ok(await question("Will the test eventually pass verification? "+ACCEPT_HINT));
    header = `// RUN: ${(shouldVerify ? "" : "%exits-with 1 ")}%baredafny verify %args "%s" > "%t"\n`;
    programArguments = "verify";
  }
  header += `// RUN: %diff "%s.expect" "%t"\n\n`;
  programReproducingError = header + programReproducingError;
  return {programReproducingError, languageServerDiagnostic, languageServerIcons, skipTestCreation};
}

// Reads an existing test and extract the last dafny command to run
async function getTestArguments(testFile) {
  var testFileContent = await fs.promises.readFile(testFile, { encoding: "utf8" });
  // Find '// RUN: %dafny_0 ... "%s" > "%t"' in testFileContent
  // and return what's in the ellipsis
  var match = testFileContent.match(/\/\/ RUN: %dafny(?:_0)?\s+([\s\S]+?)\s+"%s"(?![\s\S]*\/\/ RUN: %(bare)?dafny)/);
  if(match == null) {
    var match = testFileContent.match(/\/\/ RUN: %baredafny\s+(build|run|verify) %args(?:_0)? ([\s\S]+?)\s+"%s"(?![\s\S]*\/\/ RUN: %(bare)?dafny)/);
    if(match == null) {
      return "verify";
    } else {
      return match[1] + " " + match[2];
    }
  } else {
    return match[1];
  }
}

// Creates the two test files
async function createTestFilesAndExpect(testFile, testFileExpect, testFileContent, executionSucceeds = true) {
  await fs.promises.writeFile(testFile, testFileContent);
  await fs.promises.writeFile(testFileExpect, executionSucceeds ? `
Dafny program verifier finished with TODO verified, TODO errors
` : "");
}

// Provides help if DafnyCore.dll cannot be overwritten
async function helpIfDllLock(output) {
  if(typeof output == "object") {
    output = output.stdout + output.stderr;
  }
  const notWindows = process.platform == 'darwin';
  
  for(let dll of ["DafnyCore.dll", "DafnyLanguageServer.dll"]) {
    if(output.match(new RegExp(`warning MSB3026: Could not copy.*${dll}' because it is being used by another process`))) {
      console.log(`Looks like ${dll} is locked by another process. Let's find out which one.`);
      // If we are on Windows, it's a different command
      var command = notWindows ? `lsof -w -Fp Binaries/${dll}` : "tasklist.exe -m "+dll;
      // Run the command and report to the user what they need to do
      var processLocking = (await execLog(command, `Finding which process is locking "+dll+"`)).stdout;
      console.log(processLocking);
      if((match = /\d{4}\d*/.exec(processLocking)) &&
         ok(await question(`Do you want to kill the process ${match[0]}? ${ACCEPT_HINT}`))) {
        if(notWindows) {
          await execLog(`kill -9 ${match[0]}`, `Killing process ${match[0]}`);
        } else {
          await execLog(`taskkill /F /PID ${match[0]}`, `Killing process ${match[0]}`);	
        }
        console.log(`You can start the script again. If this occurs again, you might want to close VSCode.`);
      } else {
        console.log(`Please close the process that is locking ${dll} and then press restart the command.`);
      }
    }
  }
}

// Build the Dafny solution
async function buildSolution(issueNumber) {
  var output = await execLog("dotnet build Source/Dafny.sln", `Rebuilding Dafny to work on issue #${issueNumber}`);
  await helpIfDllLock(output);
}

// Open the given file in its default editor.
function openAndYield(cmd) {
  var start = (process.platform == 'darwin'? 'open': process.platform == 'win32'? 'start': 'xdg-open');
  execLog(`${start} ${cmd}`, `Opening file ${cmd}`);
}

// Creates the branch for the given issue number, and add all the provided test files to it.
async function createBranchAndAddTestFiles(testManagers, branchName, skipTestCreation) {
  await execLog(`git checkout -b ${branchName}`, `Creating branch ${branchName}...`);
  if(!skipTestCreation) {
    for(let testManager of testManagers) {
       await testManager.addToGit();
    }
  }
  await execLog(`git commit -m "Add test for issue #${testManagers[0].issueNumber}"`, "Committing files...");
}

// Verify if the tests of the given branch pass
async function verifyFix(testManagers) {
  var testResult = "";
  var verified = true;
  var testManagerVerified = false;
  for(let testManager of testManagers) {
    if(await testManager.exists()) {
      var testCmd = await testManager.xunitTestCmd();
      console.log("Running:"+testCmd);
      var testManagerResults = await execLog(testCmd, "\nCompiling and verifying the fix for "+testManager.type+"... (looping forever means bug)", false);
      testManagerResults = testManagerResults.stdout + testManagerResults.stderr;
      testManagerVerified = testManagerResults.match(/Failed:\s*0\s*,\s*Passed:\s*(?!0)/);
      testResult += testManagerResults;
    } else {
      testManagerVerified = true;
    }
    verified = verified && testManagerVerified;
  }
  return {ok: verified, log: testResult};
}

// Returns true if this branch was already pushed
async function originAlreadyExists(branchName) {
  var testOrigin = await execLog(`git log origin/${branchName}..${branchName}`, "Look at whether this branch was pushed previously...", false);
  testOrigin = testOrigin.stdout + testOrigin.stderr;
  return testOrigin.match(/unknown revision or path not in the working tree/) == null;
}

// Asks for the release notes lines, while providing the current issue's title as input to the user.
async function getReleaseNotesLine(issueNumber) {
  console.log("Getting the previous issue title...");
  var js = await getOriginalDafnyIssue(issueNumber);
  var releaseNotesLine = js.title;
  if(releaseNotesLine === undefined) {
    console.log(`Could not retrieve issue #${issueNumber}'s title but that's ok. Got this instead`, js);
  } else {
    console.log("This was the title of the issue: '" + releaseNotesLine + "'");
  }
  releaseNotesLine = await question("What should we put in the release notes?\nFix: ");
  return releaseNotesLine;
}

// Add the docs/dev/news/<issueNumber>.fix file
async function addTownCrierEntry(issueNumber, releaseNotesLine) {
  var towncrier = `docs/dev/news/${issueNumber}.fix`;
  if(!fs.existsSync(towncrier)) {
    await execLog(`touch ${towncrier}`, `Creating file ${towncrier}`);
    await execLog(`git add ${towncrier}`, `Adding file ${towncrier}`);
  }
  await fs.promises.writeFile(towncrier, releaseNotesLine);
}

async function listAll(pattern, message) {
  var testFiles = await execLog(`ls ${pattern}`, null, false);
  if(testFiles == ABORTED || !("stdout" in testFiles)) {
    return [];
  }
  testFiles = testFiles.stdout.split("\n").map(file => file.trim());
  return testFiles;
}

// Ads all files matching the given pattern to git.
async function addAll(patterns, message) {
  var testFiles = [];
  for(let pattern of patterns) {
    testFiles = testFiles.concat(await listAll(pattern, message));
  }
  var toAdd = testFiles.join(" ");
  await execLog(`git add ${toAdd}`, "Adding all "+message+" to git...");
}

// Add all the files, commit them and push them.
async function commitAllAndPush(testInfo, commitMessage, branchName, testsNowExist) {
  if(testsNowExist) {
    await testInfo.addToGit();
  }
  await execLog(`git commit -am \"${commitMessage}\"`, "Committing the fix (and dotnet format)...", false);
  await execLog(`git commit -am \"${commitMessage}\"`, "Just ensuring the fix is committed in case there was formatting involved...", false);
  await execLog(`git push origin --set-upstream ${branchName}`, "Pushing the fix to GitHub...");
}

// A test testManager either considers
// - A pair of git-issues/git-issue-<issuenumber>.dfy and its expect file
// - A simple [TestMethod] in DiagnosticsTest.cs and its assertions.

// A branch can list several tests to consider. All need to run correctly.

function getIntegrationTestManager(issueNumber, issueKeyword, suffix = "") {
  return {
    type: "integration-test",
    shortName: `git-issues/git-issue-${issueNumber}${suffix}.dfy`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
    // This one are private
    name: getIntegrationTestFileName(issueNumber, suffix),
    nameExpect: getIntegrationTestFileExpectName(issueNumber, suffix),
    async exists() {
      return fs.existsSync(this.name);
    },
    async create(content) {
      if(await this.exists()) {
        var suffix = "abcdefghijklmnopqrstuvwxyz";
        var indexSuffix = 0;
        var testInfo = null;
        while(indexSuffix < suffix.length &&
              fs.existsSync(getIntegrationTestFileName(this.issueNumber, suffix[indexSuffix]))) {
          indexSuffix++;
        }
        if(indexSuffix == suffix.length) {
          console.log("You have too many test cases for this issue. Please merge some.");
          throw ABORTED;
        }
        suffix = suffix[indexSuffix];
        this.name = getIntegrationTestFileName(issueNumber, suffix);
        this.nameExpect = getIntegrationTestFileExpectName(issueNumber, suffix)
      }
      console.log(`Going to create the test files ${this.name} and ${this.nameExpect}...`);
      await createTestFilesAndExpect(this.name, this.nameExpect, content);
    },
    openAndYield() {
      openAndYield(this.name);
      openAndYield(this.nameExpect);
    },
    async displayXunitTestCmd() {
      console.log((await this.xunitTestCmd()).replace(/csproj --filter/g, "csproj \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      var programArguments = await getTestArguments(this.name);
      var issueNumber = this.issueNumber;
      var issueKeyword = this.issueKeyword;
      var testFile = this.name;
      console.log("-------------------------------------------------------------");
      console.log("| Ensure you put the path of the language server for VSCode:|");
      console.log(`Dafny: Language Server Runtime Path:\n${process.cwd()}/Binaries/DafnyLanguageServer.dll`);
      console.log("-------------------------------------------------------------");
      console.log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd();
      console.log("-------------------------------------------------------------");
      console.log("| Run dafny on the file directly:                           |");
      console.log("dotnet build Source/DafnyDriver/DafnyDriver.csproj");
      console.log(`./Binaries/Dafny ${programArguments} \"${testFile}\"`);
      console.log("-------------------------------------------------------------");
      console.log("| Create a test configuration in Rider:                     |");
      console.log(`Name:  git-issue-${issueNumber}-${issueKeyword}`);
      console.log("Project:   Dafny");
      console.log("Framework: net6.0");
      console.log(`Exe path:  ${process.cwd()}/Binaries/Dafny.exe`);
      console.log(`Arguments: ${programArguments} "${testFile}"`);
      console.log("Directory: "+process.cwd());
      console.log("-------------------------------------------------------------");
    },
    patternsToAddToGit() {
      return [ getIntegrationTestFileName(issueNumber, "*"),
               getIntegrationTestFileExpectName(issueNumber, "*")];
    },
    async addToGit() {
      await addAll(this.patternsToAddToGit(), "the integration test files");
    },
    // Returns the command to test all the tests that this branch depends on, on dotnet
    async xunitTestCmd() {
      var issueNumber = this.issueNumber;
      // List all the log messages since the branch was created
      var cmd = "git log --oneline --no-merges --pretty=format:%s origin/master..HEAD";
      // Execute the command above using execLog
      var output = (await execLog(cmd, "Listing all the log messages since the branch was created...")).stdout;
      // Keep only the lines of output that start with FIXER:, remove any single quotes on the be and remove the prefix
      var lines = output.split("\n").filter(l => l.startsWith("FIXER:")).map(l => l.substring(6));
      // Split every item by spaces and flatten the result
      var moreTestCases = [].concat.apply([], lines.map(l => l.split(" ")));
      // Prefix every test case with "|DisplayName~" and concatenate everything
      var testCases = moreTestCases.map(t => "|DisplayName~" + t).join("");
      return `dotnet test -v:n Source/IntegrationTests/IntegrationTests.csproj --filter "DisplayName~git-issues/git-issue-${issueNumber}${testCases}"`;
    }
  };
}

function getLanguageServerDiagnosticTestManager(issueNumber, issueKeyword, name = "") {
  const testTemplate = (methodName, content) => `[TestMethod]
    public async Task ${methodName}() {
      var source = @"
${content.replace(/"/g,"\"\"")}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      // Uncomment what you need.
      // var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      // Assert.AreEqual(1, diagnostics.Length);
      // ApplyChange(ref documentItem, ((0, 0), (3, 0)), "insert text");
      // diagnostics = await GetLastDiagnostics(documentItem, CancellationToken); // If expect no parsing error
      // diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken); // If expect parsing errors
      // Assert.AreEqual(0, diagnostics.Length);
      
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }
    
    `;
  return getLanguageServerManager("Synchronization/DiagnosticsTest.cs", testTemplate, issueNumber, issueKeyword, name);
}

function getLanguageServerGutterIconsManager(issueNumber, issueKeyword, name = "") {
  const testTemplate = (methodName, content) => `[TestMethod]
  public async Task ${methodName}() {
    await VerifyTrace(@"
${content.replace(/"/g,"\"\"")}", intermediates: false);
  }
 
  `;
  return getLanguageServerManager("GutterStatus/SimpleLinearVerificationGutterStatusTester.cs", testTemplate, issueNumber, issueKeyword, name);
}


function getLanguageServerManager(fileName, testTemplate, issueNumber, issueKeyword, name = "") {
  if(name == "") {
    name = issueKeyword.replace(/^\w|-+(\w)/g, match => match.length == 1 ? match.toUpperCase() : match[1].toUpperCase());
  }
  return {
    type: "language-server at "+fileName,
    shortName: `Test named 'GitIssue${issueNumber}${name}' in DafnyLanguageServer.Test/${fileName}`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
    testMethodName: "GitIssue"+issueNumber,
    testFile: `Source/DafnyLanguageServer.Test/${fileName}`,
    testFileContent: null,
    regex: /public\s+async\s+Task\s*(GitIssue(\d+)\w+)\(\)\s*\{/g,
    existingTests: null,
    name: name,
    async recoverData() {
      if(!this.testFileContent) {
        this.testFileContent = await fs.promises.readFile(this.testFile, "utf-8");
      }
      if(!this.testFileContent) {
        console.log("Could not find " + this.testFile);
      }
      if(this.existingTests == null) {
        this.existingTests = [];
        this.regex.lastIndex = 0;
        while(match = this.regex.exec(this.testFileContent)) {
          if(match[2] == issueNumber + "") {
            this.existingTests.push(match[1]);
          }
        }
      }
      this.MethodName = this.existingTests[0]; // Might be null
      this.MethodName = this.rawMethodName();
    },
    rawMethodName() {
      return this.MethodName != null ? this.MethodName.replace(/[A-Z]$/, "") : null;
    },
    async exists() {
      await this.recoverData();
      return this.existingTests.length > 0;
    },
    async create(content) {
      await this.recoverData();
      var firstTestMatch = /\[TestMethod\]/.exec(this.testFileContent);
      if(!firstTestMatch) {
        console.log(`Could not find [TestMethod] in ${this.testFile}`);
        throw ABORTED;
      }
      var i = firstTestMatch.index;
      this.MethodName = "GitIssue" + this.issueNumber + this.name;
      if(this.testFileContent.indexOf(this.MethodName) >= 0) {
        var suffix = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        var indexSuffix = 0;
        while(indexSuffix < suffix.length && this.testFileContent.indexOf("GitIssue" + this.issueNumber + this.name + suffix[indexSuffix]) >= 0) {
          indexSuffix++;
        }
        if(indexSuffix >= suffix.length) {
          console.log("Too many DafnyLanguageServer test files prefixed by "+MethodName);
          throw ABORTED;
        }
        this.MethodName = "GitIssue" + this.issueNumber + this.name + suffix[indexSuffix];
      }
      var newTestFileContent = this.testFileContent.substring(0, i) + testTemplate(this.MethodName, content)+this.testFileContent.substring(i);

      console.log(`Going to add test ${this.MethodName} in ${this.testFile}...`);
      await fs.promises.writeFile(this.testFile, newTestFileContent);
    },
    openAndYield() {
      openAndYield(this.testFile);
      console.log("Look for "+this.MethodName+"! It should be the first test.");
    },
    async displayXunitTestCmd() {
      console.log((await this.xunitTestCmd()).replace(/Test --filter/g, "Test \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      await this.recoverData();
      console.log("-------------------------------------------------------------");
      console.log("| Ensure you put the path of the language server for VSCode:|");
      console.log(`Dafny: Language Server Runtime Path:\n${process.cwd()}/Binaries/DafnyLanguageServer.dll`);
      console.log("-------------------------------------------------------------");
      console.log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd()
      console.log("-------------------------------------------------------------");
      console.log("| Run the test in Rider:                                    |");
      console.log(this.MethodName);
      console.log("-------------------------------------------------------------");
    },
    patternsToAddToGit() {
      return [ this.testFile ];
    },
    async addToGit() {
      await addAll(this.patternsToAddToGit(), fileName);
    },
    async xunitTestCmd() {
      return `dotnet test --nologo Source/DafnyLanguageServer.Test --filter Name~${this.rawMethodName()}`;
    }
  };
}

function getIntegrationTestFileName(issueNumber, suffix = "") {
  return `Test/git-issues/git-issue-${issueNumber}${suffix}.dfy`;
}
function getIntegrationTestFileExpectName(issueNumber, suffix = "") {
  return getIntegrationTestFileName(issueNumber, suffix)+".expect";
}
// Adds one more existing test to the branch by adding it in an empty commit.
async function doAddExistingIntegrationTest(testName) {
  // List all the files in Test/ that contain "testName", which might contain a directory separator
  var testFiles = await execLog(`find Test/ -name "*.dfy"`, "Listing all the test files that contain "+testName);
  testFiles = testFiles.stdout.split("\n").map(file => file.trim());
  // Remove "Test/" from the prefix of each file
  testFiles = testFiles.map(file => file.substring(5));
  var testFile = testFiles.filter(file => file.indexOf(testName) >= 0);
  if(testFile.length == 0) {
    console.log("Could not find the test file for "+testName);
    throw ABORTED;
  } else {
    console.log(`The following test file${testFile.length > 1 ? "s" : ""} will be added:`);
    for(var file of testFile) {
      console.log(file);
    }
    if(!ok(await question(`Confirm? ${ACCEPT_HINT}`))) {
      return;
    }
    var commitMessage = `FIXER:${testFile.join(" ")}`;
    await execLog(`git commit --only --allow-empty -m "${commitMessage}"`, "Adding the tests files...");
  }
}
// Process `fix more` with the given detected issueNumber, and moreText is the argument after "more".
async function doAddExistingOrNewTest(testInfo, testInfoLSDiagnostic, testInfoLSIcons, moreText) {
  var otherIssueNumber = moreText || await question("Please enter either\n-Another existing issue number from which to import tests\n-The name of an existing integration test\n-Blank if you want to create a new test manually\n");
  if(otherIssueNumber != "" && !otherIssueNumber.match(/^\d+$/)) {
    console.log("The issue number seems to be an existing integration test case. Adding them to this branches' tests...");
    return await doAddExistingIntegrationTest(otherIssueNumber);
  }
  
  var {programReproducingError, languageServerDiagnostic, languageServerIcons, skipTestCreation} =
    await interactivelyCreateTestFileContent(otherIssueNumber);
  if(skipTestCreation) {
    throw ABORTED;
  }
  if(languageServerDiagnostic) {
    testInfoLSDiagnostic.create(programReproducingError);
    testInfoLSDiagnostic.openAndYield();
  } else if(languageServerIcons) {
    testInfoLSIcons.create(programReproducingError);
    testInfoLSIcons.openAndYield();
  } else {
    testInfo.create(programReproducingError);
    testInfo.openAndYield();
  }
}

// We will want to run tests on the language server at some point
// (DafnyLanguageServer/Synchronization/DiagnosticsTest.cs).

// The main function
async function Main() {
  var {openFiles, skipVerification, addOneTestCase, args} = processArgs();
  var fixBranchDidExist = false;
  var testFileContent = "";
  var languageServerDiagnostic = false;
  var languageServerIcons = false;
  var skipTestCreation = false;
  var providedIssueNumber = args[2];
  var providedKeywordNumber = args[3];
  var providedContent = args[4]; // Should deprecate. No one is ever going to add a test content as an argument of the command line.
  try {
    var existingBranch = await ensureMasterOrFollowupFix(providedIssueNumber, addOneTestCase);
    var {issueNumber, issueKeyword, neededToSwitchToExistingBranch, fixBranchDidExist} =
      await getIssueNumberAndKeyword(existingBranch, providedIssueNumber, providedKeywordNumber);
    var branchName = `fix-${issueNumber}-${issueKeyword}`;

    // There might be both integration tests and language server tests.
    // There might be multiple integration tests and multiple language server tests.

    // We first detect if tests related to the branch exist. If not such file exist, then

    var testInfo = getIntegrationTestManager(issueNumber, issueKeyword);
    var testInfoLSDiagnostic = getLanguageServerDiagnosticTestManager(issueNumber, issueKeyword);
    var testInfoLSIcons = getLanguageServerGutterIconsManager(issueNumber, issueKeyword);
    var testManagers = [testInfo, testInfoLSDiagnostic, testInfoLSIcons];
    var testFilesDidExist = addOneTestCase;
    for(let i = 0; i < testManagers.length; i++) {
      testFilesDidExist = testFilesDidExist || await testManagers[i].exists();
    }
    if(!testFilesDidExist) {
      addOneTestCase = false; // This will be automatic
      var {programReproducingError: testFileContent, languageServerDiagnostic, languageServerIcons, skipTestCreation} =
        await interactivelyCreateTestFileContent(issueNumber, providedContent);
      if(!skipTestCreation) {
        if(languageServerDiagnostic) {
          await testInfoLSDiagnostic.create(testFileContent);
        } else if(languageServerIcons) {
          await testInfoLSIcons.create(testFileContent);
        } else {
          await testInfo.create(testFileContent);
        }
      }
    }
    var testsNowExist = testFilesDidExist || !skipTestCreation;
    if(addOneTestCase) {
      await doAddExistingOrNewTest(testInfo, testInfoLSDiagnostic, testInfoLSIcons, providedIssueNumber);
    }

    if(!skipTestCreation && (!fixBranchDidExist || openFiles || neededToSwitchToExistingBranch)) {
      for(let testManager of testManagers) {
        if(await testManager.exists()) {
          testManager.openAndYield();
        }
      }
    }
    if(neededToSwitchToExistingBranch) { // We opened the files previously, but we rebuild the solution afterwards. Is that ok?
      await buildSolution(issueNumber);
    }

    if(!fixBranchDidExist) {
      await createBranchAndAddTestFiles(testManagers, branchName, skipTestCreation);
    }
    if(testsNowExist) {
      for(let testManager of testManagers) {
        if(await testManager.exists()) {
          await testManager.displayRunHelp();
        }
      }
    }
    if((!fixBranchDidExist || !testFilesDidExist || openFiles) &&
        (!skipVerification || !skipTestCreation)) {
      var withoutOpen = open ? " (without 'open')" : "";
      console.log(`All set! Now focus on making the test git-issues/git-issue-${issueNumber}.dfy to pass. You can add additional tests such as git-issues/git-issue-${issueNumber}.dfy`);
      console.log(`When the tests succeed, re-run this script to verify the fix and create the PR.\nYou can run the same command-line${withoutOpen}.`);
    } else {
      var testResult = {};
      if(skipVerification || ((testResult = await verifyFix(testManagers), testResult.ok)) && !neededToSwitchToExistingBranch) {
        var wasPushed = await originAlreadyExists(branchName);
        if(skipVerification) {
          console.log(`You indicated "force", so you assume that this commit solves the issue #${issueNumber}.`);
        } else {
          console.log(`\nCongratulations for ${wasPushed ? "ensuring this new commit still solves" : "solving"} issue #${issueNumber}!`);
        }

        if(!wasPushed && !ok(await question("Are you ready to create the PR? " + ACCEPT_HINT))) {
          throw ABORTED;
        }
        var commitMessage = "";
        if(!wasPushed) {
          var releaseNotesLine = await getReleaseNotesLine(issueNumber);
          await addTownCrierEntry(issueNumber, releaseNotesLine);
          var prContent = `This PR fixes #${issueNumber}\nI added the corresponding test.\n\n<small>By submitting this pull request, I confirm that my contribution is made under the terms of the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).</small>`;
          commitMessage = `Fix: ${releaseNotesLine}`;
        } else {
          commitMessage = await question("What should be the commit message?\n");
        }
        await commitAllAndPush(testInfo, commitMessage, branchName, testsNowExist);
        if(!wasPushed) {
          var url = `https://github.com/dafny-lang/dafny/compare/${branchName}?expand=1&title=`+encodeURIComponent(commitMessage)+"&body="+encodeURIComponent(prContent);
          console.log("Opening the browser to create a PR at this URL...:\n"+url);
          await open(url);
          console.log("Look at your browser, it should be opened.");
        } else {
          console.log("Updated the PR.");
        }
      } else {
        if(neededToSwitchToExistingBranch && testResult.ok) {
          console.log("The tests are passing as expected. Run 'fix' when you have something new to verify.\n");
        } else {
          console.log(testResult.log);
          console.log("The test did not pass. Please fix the issue and re-run this script after ensuring that the following command-line succeeds:\n");
          for(let testManager of testManagers) {
            if(await testManager.exists()) {
              testManager.displayXunitTestCmd();
            }
          }
          await helpIfDllLock(testResult.log);
        }
      }
    }
  } catch(e) {
    if(e != ABORTED) {
      throw e;
    }
  } finally {
    close();
  }
}

Main();