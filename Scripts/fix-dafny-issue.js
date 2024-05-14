#!/usr/bin/env node

const help = `
 * 'fix' makes it possible to fix a Dafny bug reported in GitHub in no time.
 * Add the following alias in your bash profile:
 * 
 *     alias fix='node scripts/fix-dafny-issue.js'
 * 
 * The first time you use this command, look up for an issue number of GitHub you want to solve, and enter:
 * 
 *     > fix <issueNumber>
 * 
 * This script automates the administrative process of fixing the issue. It will
 * - Ask you for the issue number, and an issue keyword (optionally accepts issue keyword as second argument)
 * - Fetch the faulty code of the issue if it is in a dafny code block
 * - Depending on the label, confirm and add the test to either integration tests,
 *   language server tests, formatting tests or LSP icons tests,
 * - Create a branch named 'fix-<issueNumber>-<issueKeyword>', and commits the tests there immediately
 * - Provide you with information to debug the issue in Rider, in CLI dotnet, or just run Dafny.
 * 
 * Now you're all set and you can go ahead and fix the issue. When you've made progress,
 * enter the command
 * 
 *     > fix
 * 
 * and press ENTER (with an optional --message "<commit message>" argument). The script will
 * - Compile Dafny and run the tests associated to the issue you are fixing
 * - If all the tests pass, ask you if you want to commit and push the changes.
 *   If you accept:
 * - Create the \`doc/dev/news/<issueNumber>.fix\` file for you the first time, asking you about its content
 * - Add all new and modified files
 *   (including other \`git-issue-<issueNumber><suffix>.dfy\` files)
 * - Commit and pushes the changes
 * - Open your browser If the first time it's pushed) with a page
 *   to create the PR with the title and description already populated.
 * 
 * If you want to switch to another issue that uses the same branch format as this script does,
 * ensure the working directory is clean, and run
 * 
 *     > fix <existing issue number | PR number | keyword>
 * 
 * The script will:
 * - Find and checks out the branch matching the issue number, the PR number, or a keyword
 * - Open the test files in their respective editors (for CI tests only)
 * - Ask if it can rebuilds the solution and do accordingly
 * - Provide you with information on how to test the issue.
 * 
 * If you are already in the issue branch and you want to re-open
 * the test files (because you closed them...), enter
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
 *     > fix more|add <optional existing issue # or existing test name>
 * 
 * If you just write \`fix more\` or \`fix add\`, you will be prompted for the argument.
 * - Providing a number will let you import another GitHub issue.
 * - Providing an existing integration test name pattern will ensure that all these
 *   selected tests are run when you run \`fix\` without arguments.
 *   If more than one test is found, you'll be prompted to confirm your choices.
 * 
 * If you want to run an integration test, enter
 * 
 *     > fix run <any integration test keyword>
`;
ToRootFolder();
// Not sure why but constants are not accessible after an eval(), but functions are
function constants() {};

// To add a new test type, start by adding one field here, and follow the fields.
const TEST_TYPE = {
  SKIP_TEST_CREATION: 0,
  INTEGRATION: 1,
  LANGUAGE_SERVER: 2,
  LANGUAGE_SERVER_ICONS: 3,
  FORMATTER: 4
}
constants.TEST_TYPE = TEST_TYPE;

const TEST_FOLDER = "Source/IntegrationTests/TestFiles/LitTests/LitTest/";

const ABORTED = "ABORTED";
const FINISHED = "FINISHED";
const ACCEPT_HINT = "(ENTER or y for yes, n for no, CTRL+C to abort)\n> ";
constants.ABORTED = ABORTED;
constants.FINISHED = FINISHED;
constants.ACCEPT_HINT = ACCEPT_HINT;
const { exit } = require('process');
const readline = require('readline');
const root = require('child_process').execSync('npm root -g').toString().trim();
const fs = require('fs');
let fetch = loadGlobalModule('cross-fetch');
let open = loadGlobalModule('open');
const { promisify } = require('util');
const exec = require('child_process').exec;
const execAsync = promisify(exec);
const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout
});
let cache = {};
constants.cache = cache;
let questionCache = {}; // Used for tests only.
constants.questionCache = questionCache;
// Ask the given question and returns the answer of the user
const question = function(input) {
  if(Object.keys(constants.questionCache).length > 0) {
    if(input in constants.questionCache) {
      return new Promise((resolve, reject) => {
        resolve(constants.questionCache[input]);
      });
    } else {
      return new Promise((resolve, reject) => {
        reject("Could not find question\n" + JSON.stringify(input) + "\nin the test");
      });
    }
  }
  return new Promise((resolve, reject) => {
    rl.question(input, resolve);
  });
}
constants.logTest = null;
let log = function() {
  if(constants.logTest !== null) {
    for(var i = 0; i < arguments.length; i++) {
      if(i > 0) {
        constants.logTest += " ";
      }
      constants.logTest += arguments[i];
    }
  } else {
    console.log(...arguments);
  }
}

Main();
//////// Folder tools

// Returns the loaded module that should be installed globally.
function loadGlobalModule(nameAfterRoot) {
  try {
    return require(root + '/' + nameAfterRoot);
  } catch(e) {
    log("Module " + nameAfterRoot + " must be installed globally. Run `npm install -g " + nameAfterRoot + "`");
    exit(1);
  }
}

// Ensures that the script is executed in the root of the dafny repository
function ToRootFolder() {
  if(process.cwd().endsWith("scripts")) {
    process.chdir("..");
  }
}

// Displays the hint and execute the command.
// If an exception occurs, logs it and return ABORTED if returnAbortedIfFailure, otherwise returns the exception
// Returns the output of the command
async function execLog(cmd, hint, returnAbortedIfFailure=true) {
  if(hint) {
    log(hint);
  }
  var output = "";
  try {
    output = await execAsync(cmd);
  } catch(e) {
    if(returnAbortedIfFailure) {
      log(e);
      return ABORTED;
    } else {
      return e;
    }
  }
  return output;
}

// Returns true iff there is no pending changes on the current branch
async function ensureWorkingDirectoryClean() {
  var unstagedChanges = (await execAsync("git diff")).stdout.trim() + (await execAsync("git diff --cached")).stdout.trim();
  if(unstagedChanges != "") {
    return false;//log("Please commit your changes before launching this script.");
  }
  return true;
}


// Returns true if the answer can be interpreted as a "yes", with an empty string defaulting to yes.
function ok(answer) {
  return answer.toLowerCase().substring(0, 1) == "y" || answer == "";
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
      log("You are currently on branch " + currentBranch + " which is a fix branch for issue " + match[1] + " and keyword " + match[2]);
      return {issueNumber: match[1], issueKeyword: match[2], cleanDirectory, neededToSwitchToExistingBranch: false};
    }
  }
  if(!cleanDirectory) {
    log("Please commit your changes before launching this script.");
    throw ABORTED;
  }
  if(providedIssueNumber != null) {
    // Check if there is an existing fix branch that starts with providedIssueNumber
    var branches = (await execAsync("git branch")).stdout.trim().split("\n").map(b => b.trim());
    var existingFixBranches = branches.filter(b => b.match(new RegExp(`^fix-.*${providedIssueNumber}.*\$`)));
    if(existingFixBranch != null && existingFixBranch.length > 1) {
      log("There are multiple fix branches for issue '" + providedIssueNumber + "', please be more specific:\n" + existingFixBranches.join("\n"));
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
      log("The PR "+providedIssueNumber+" is fixing issue " +match[1] + ". Redirecting...");
      return ensureMasterOrFollowupFix(match[1]);
    }
  }
  if(currentBranch != "master") {
    log(`You need to be on the 'master' branch to create ${providedIssueNumber ? "a fix for #" + providedIssueNumber: "a fix."}`);
    if(!ok(await question(`Switch from '${currentBranch}' to 'master'? ${ACCEPT_HINT}`))) {
      log("Fixing script aborted.");
      throw ABORTED;
    }
    log("switched to master branch");
    log((await execAsync("git checkout master")).stdout);
    currentBranch = await getCurrentBranch();
    if(currentBranch != "master") {
      log("Failed to checkout master");
      throw ABORTED;
    }
  }
  await execAsync("git pull");
  log("Latest master checked out and pulled from origin.")
}

// Pull the JSON of the given issue number
async function getOriginalDafnyIssue(issueNumber) {
  if(!issueNumber.match(/^\d+$/)) {
    log(`Not an issue number: ${issueNumber}`);
    return {};
  }
  if(issueNumber in constants.cache) {
    return constants.cache[issueNumber];
  }
  log("Fetching original dafny issue #" + issueNumber);
  var js = await (await fetch("https://api.github.com/repos/dafny-lang/dafny/issues/" + issueNumber)).json();
  constants.cache[issueNumber] = js;
  return js;
}
// Skips the words "open", "force" and "more" from the arguments,
// sets the flags appropriatedly and returns the remaining of the arguments.
function processArgs() {
  var args = [...process.argv];
  var openFiles = false;
  var skipVerification = false;
  var addOneTestCase = false;
  var run = false;
  var unitTests = false;
  var defaultMessage = null;
  while(args[2] in {"open": 0, "force": 0, "more": 0, "add": 0, "run": 0, "unit-tests": 0}) {
    if(args[2] == "open" || args[2] == "add") {
      args.splice(2, 1);
      openFiles = true;
    }
    if(args[2] == "unit-tests") {
      args.splice(2, 1);
      unitTests = true;
    }
    if(args[2] == "force") {
      args.splice(2, 1);
      skipVerification = true;
    } else if(args[2] == "run") {
      args.splice(2, 1);
      run = true;
    } else if(args[2] == "add" || args[2] == "more") { // "more"
      args.splice(2, 1);
      addOneTestCase = true;
    }
  }
  if(args[2] == "--help") {
    log(help);
    process.exit(0);
  }
  if(args[2] == "--message") {
    if(args.length < 4) {
      log("Missing message");
      process.exit(1);
    }
    defaultMessage = args[3];
    args.splice(2, 2);
  }
  if(args[2] != null && args[2].startsWith('--')) {
    log("This script does not take options except --help and --message. Did you mean `fix "+args[2].substring(2)+"`?");
    process.exit(0);
  }
  return {args, openFiles, skipVerification, addOneTestCase, defaultMessage, run, unitTests};
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
      log("Getting issue keyword...");
      issueKeyword = await getIssueKeyword(issueNumber);
    }
    if(issueKeyword != null && issueKeyword != "") {
      log("The suggested issue keyword is the following:\n"+issueKeyword);
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
      log("Did not obtain a suitable issue keyword");
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
    .replace(/[^a-zA-Z0-9]+/g, "-") : "";
  while(issueKeyword.indexOf("-") >= 0 && issueKeyword.length > 50) {
    issueKeyword = issueKeyword.replace(/-[^-]*$/, "");
  }
  if(issueKeyword.length > 50) {
    issueKeyword = issueKeyword.substring(0, 50);
  }
  return issueKeyword;
}

// Returns true if the given json structure has the expected label.
// Useful to classify an issue and provide a good default choice
function hasLabel(js, labelName) {
  return ("labels" in js && js.labels.find(label => 
    label.name.indexOf(labelName) >= 0)) ? true : false;
}

function extractProgram(js) {
  // Get the body field of the first post
  var issueContent = "body" in js ? js.body : "";
  // extract the code contained between ```dafny and ```
  var match = issueContent.match(/```(?:.*dafny)?\r?\n([\s\S]+?)\r?\n```/);
  var programReproducingError = match != null ? match[1] : "";
  return programReproducingError;
}

// Create the tests fore the given issue number
async function interactivelyCreateTestFileContent(issueNumber = null, commandLineContent = null) {
  // Retrieve the content of the first post from the issue
  var js = issueNumber != null && issueNumber != "" ? await getOriginalDafnyIssue(issueNumber) : {};
  
  var hasLanguageServerLabel = hasLabel(js, "language-server");
  var hasFormatterLabel = hasLabel(js, "formatter");
  var programReproducingError = extractProgram(js);
  var hasMain = programReproducingError.match(/method\s+Main\s*\(/);
  var isDefault = !hasLanguageServerLabel && !hasFormatterLabel;
  var type = await(question(`Do you want to reproduce this problem\n- On the command line (${isDefault ? "ENTER or " : ""}1)\n`+
      `- A diagnostic test on the language server(${hasLanguageServerLabel ? "ENTER or " : ""}2)\n`+
      `- A formatter test (${hasFormatterLabel ? "ENTER or " : ""}3)\n`+
      `- A gutter icons test on the language server (4)\n`+
      `- Don't create test files(5)?\n> `));
  var test_type =
  (hasLanguageServerLabel && type == "") || type == "2" ? TEST_TYPE.LANGUAGE_SERVER :
      (hasFormatterLabel && type == "") || type == "3" ? TEST_TYPE.FORMATTER :
        (type == "4" ? TEST_TYPE.LANGUAGE_SERVER_ICONS :
          (type == "5" ? TEST_TYPE.SKIP_TEST_CREATION :
            TEST_TYPE.INTEGRATION));
  if(test_type == TEST_TYPE.SKIP_TEST_CREATION) {
    return {programReproducingError, test_type};
  }
  var shouldCompile = test_type == TEST_TYPE.INTEGRATION && ok(await question("Will the test need to be compiled? "+ACCEPT_HINT));
  var shouldRun = shouldCompile && (hasMain || ok(await question("Will the test need to be run (i.e. will have a Main() method)? "+ACCEPT_HINT)));
  if(shouldCompile) {
    log("All backends are going to be tested. If you want to modify the output of a particular backend or ignore one, please check "+TEST_FOLDER+"README.md.");
  }

  programReproducingError = programReproducingError == "" ?
    (commandLineContent ?? (
      shouldRun ? "method Main() {\n  \n}" : "")) : programReproducingError;
  if(test_type != TEST_TYPE.INTEGRATION) {
    return {programReproducingError, test_type};
  }
  var header = "";
  if(shouldCompile) {
    if(shouldRun) {
      header += `// RUN: %testDafnyForEachCompiler "%s"\n\n`;
    } else {
      var c = "build";
      header += `// RUN: %baredafny verify %args "%s" > "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:cs "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:js "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:cpp "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:java "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:go "%s" >> "%t"\n`;
      header += `// RUN: %baredafny ${c} %args --no-verify -t:py "%s" >> "%t"\n`;
      header += `// RUN: %diff "%s.expect" "%t"\n\n`;
    }
  } else {
    var shouldVerify = ok(await question("Will the test eventually pass verification? "+ACCEPT_HINT));
    var shouldResolve = shouldVerify || ok(await question("Will the test eventually pass resolution? "+ACCEPT_HINT));
    header = `// RUN: ${(shouldVerify ? "" : (shouldResolve ? "%exits-with 4 " : "%exits-with 2 "))}%baredafny verify %args "%s" > "%t"\n`;
    header += `// RUN: %diff "%s.expect" "%t"\n\n`;
  }
  programReproducingError = header + programReproducingError;
  return {programReproducingError, test_type};
}

// Reads an existing test and extract the last dafny command to run
async function getTestArguments(testFile) {
  var testFileContent = await fs.promises.readFile(testFile, { encoding: "utf8" });
  // Find '// RUN: %dafny_0 ... "%s" > "%t"' in testFileContent
  // and return what's in the ellipsis
  var match = testFileContent.match(/\/\/ RUN: (?:%exits-with \d+ )?%dafny(?:_0)?\s+([\s\S]+?)\s+"%s"(?![\s\S]*\/\/ RUN: %(bare)?dafny)/);
  if(match == null) {
    var match = testFileContent.match(/\/\/ RUN: (?:%exits-with \d+ )?%baredafny\s+(build|run|verify) %args(?:_0)?([\s\S]+?)"%s"(?![\s\S]*\/\/ RUN: %(bare)?dafny)/);
    if(match == null) {
      var match = testFileContent.match(/\/\/ RUN: %testDafnyForEachCompiler/);
      return "run -t go/cs/js/java/py/cpp";
    } else {
      return (match[1] + " " + match[2]).trim();
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
    if(output && output.match(new RegExp(`warning MSB3026: Could not copy.*${dll}' because it is being used by another process`))) {
      log(`Looks like ${dll} is locked by another process. Let's find out which one.`);
      // If we are on Windows, it's a different command
      var command = notWindows ? `lsof -w -Fp Binaries/${dll}` : "tasklist.exe -m "+dll;
      // Run the command and report to the user what they need to do
      var processLocking = (await execLog(command, `Finding which process is locking "+dll+"`)).stdout;
      log(processLocking);
      if((match = /\d{4}\d*/.exec(processLocking)) &&
         ok(await question(`Do you want to kill the process ${match[0]}? ${ACCEPT_HINT}`))) {
        if(notWindows) {
          await execLog(`kill -9 ${match[0]}`, `Killing process ${match[0]}`);
        } else {
          await execLog(`taskkill /F /PID ${match[0]}`, `Killing process ${match[0]}`);	
        }
        log(`You can start the script again. If this occurs again, you might want to close VSCode.`);
      } else {
        log(`Please close the process that is locking ${dll} and then press restart the command.`);
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
    for(let k in testManagers) {
      var testManager = testManagers[k];
       await testManager.addToGit();
    }
  }
  await execLog(`git commit -m "Add test for issue #${testManagers[TEST_TYPE.INTEGRATION].issueNumber}"`, "Committing files...");
}

// Verify if the tests of the given branch pass
async function verifyFix(testManagers) {
  var testResult = "";
  var verified = true;
  var testManagerVerified = false;
  for(let k in testManagers) {
    var testManager = testManagers[k];
    if(await testManager.exists()) {
      var testCmd = await testManager.xunitTestCmd();
      log("\nRunning:"+testCmd);
      var testManagerResults = await execLog(testCmd, "\nCompiling and verifying the fix for "+testManager.type+"... (not terminating sometimes means bug or need to restart 'fix')", false);
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
  log("Getting the previous issue title...");
  var js = await getOriginalDafnyIssue(issueNumber);
  var releaseNotesLine = js.title;
  if(releaseNotesLine === undefined) {
    log(`Could not retrieve issue #${issueNumber}'s title but that's ok. Got this instead`, js);
  } else {
    log("This was the title of the issue: '" + releaseNotesLine + "'");
  }
  var extension = "fix";
  releaseNotesLine = await question("What should we put in the release notes? Press ENTER if it is merely a feature\nFix: ");
  if(releaseNotesLine.trim() == "") {
    releaseNotesLine = await question("What should we put in the release notes?\nFeat: ");
    if(releaseNotesLine.trim() == "") {
      throw ABORTED;
    }
    extension = "feat";
  }
  return {releaseNotesLine,extension};
}

// Add the docs/dev/news/<issueNumber>.fix file
async function addTownCrierEntry(issueNumber, releaseNotesLine, extension) {
  var towncrier = `docs/dev/news/${issueNumber}.${extension}`;
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

async function getAllAddedTestsWithPrefix(PREFIX) {
  // List all the log messages since the branch was created
  var cmd = "git log --oneline --no-merges --pretty=format:%s origin/master..HEAD";
  // Execute the command above using execLog
  var output = (await execLog(cmd, "Listing all the log messages since the branch was created...")).stdout;
  // Keep only the lines of output that start with "PREFIX:", remove any single quotes on the be and remove the prefix
  var lines = output.split("\n").filter(l => l.startsWith(PREFIX + ":")).map(l => l.substring(PREFIX.length + 1));
  // Split every item by spaces and flatten the result
  var moreTestCases = [].concat.apply([], lines.map(l => l.split(" ")));
  // Prefix every test case with "|DisplayName~" and concatenate everything
  return moreTestCases.filter(t => t != null && t.length > 0);
}

// A test manager has several abilities
// - "exists" It can test if, given the issue number, there exist already some tests with that number
// - "create": Given some content, it can create a test file
// - "openAndYield": It can open the test files for the given issue number in their respective editors
// - "displayRunHelp": If tests exist, it display help to run them manually
// - "addToGit": Adds all the relevant tests files to git
// - "xunitTestCmd": A command to run all the tests
// - "addExisting": Given a hint, can look for existing tests and add them


function getIntegrationTestManager(issueNumber, issueKeyword, suffix = "") {
  // A test testManager either considers
// - A pair of git-issues/git-issue-<issuenumber>.dfy and its expect file
// - A simple [Fact] in DiagnosticsTest.cs and its assertions.

// A branch can list several tests to consider. All need to run correctly.

  return {
    type: "integration-test",
    shortName: `git-issues/git-issue-${issueNumber}${suffix}.dfy`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
    addedTestCases: null,
    commitPrefix: "FIXER", // Prefix to identify additional tests
    // This one are private
    name: getIntegrationTestFileName(issueNumber, suffix),
    nameExpect: getIntegrationTestFileExpectName(issueNumber, suffix),
    async recoverData() {
      if(this.addedTestCases == null) {
        this.addedTestCases = await getAllAddedTestsWithPrefix(this.commitPrefix, true);
      }
    },
    async exists() {
      await this.recoverData();
      var fileExists = this.name != null && fs.existsSync(this.name);
      return fileExists || this.addedTestCases != null && this.addedTestCases.length > 0;
    },
    async create(content) {
      if(await this.exists()) {
        var suffix = "abcdefghijklmnopqrstuvwxyz";
        var indexSuffix = 0;
        while(indexSuffix < suffix.length &&
              fs.existsSync(getIntegrationTestFileName(this.issueNumber, suffix[indexSuffix]))) {
          indexSuffix++;
        }
        if(indexSuffix == suffix.length) {
          log("You have too many test cases for this issue. Please merge some.");
          throw ABORTED;
        }
        suffix = suffix[indexSuffix];
        this.name = getIntegrationTestFileName(issueNumber, suffix);
        this.nameExpect = getIntegrationTestFileExpectName(issueNumber, suffix)
      }
      log(`Going to create the test files ${this.name} and ${this.nameExpect}...`);
      await createTestFilesAndExpect(this.name, this.nameExpect, content);
    },
    async openAndYield() {
      await this.recoverData();
      if(this.name != null && fs.existsSync(this.name)) {
        log("yes")
        openAndYield(this.name);
        openAndYield(this.nameExpect);
      }
      var suffix = "abcdefghijklmnopqrstuvwxyz";
      var indexSuffix = 0;
      while(indexSuffix < suffix.length &&
            fs.existsSync(getIntegrationTestFileName(this.issueNumber, suffix[indexSuffix]))) {
        var otherName = getIntegrationTestFileName(this.issueNumber, suffix[indexSuffix]);
        openAndYield(otherName);
        openAndYield(otherName+".expect");
        indexSuffix++;
      }
      // Plus all added tests
      if(this.addedTestCases != null) {
        // Remove DisplayName~ from the added test cases
        for(var testCase of this.addedTestCases) {
          openAndYield(TEST_FOLDER+testCase);
        }
      }

    },
    async displayXunitTestCmd() {
      log((await this.xunitTestCmd()).replace(/csproj --filter/g, "csproj \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      var testFile = this.name;
      if(testFile == null || !fs.existsSync(this.name)) {
        // Take the first file from additional
        testFile = TEST_FOLDER+this.addedTestCases[0];
      }
      var programArguments = await getTestArguments(testFile);
      var issueNumber = this.issueNumber;
      var issueKeyword = this.issueKeyword;
      log("-------------------------------------------------------------");
      log("| Ensure you put the path of the language server for VSCode:|");
      log(`Dafny: Language Server Runtime Path:\n${process.cwd()}/Binaries/Dafny.exe`);
      log("-------------------------------------------------------------");
      log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd();
      log("-------------------------------------------------------------");
      log("| Run dafny on the file directly:                           |");
      log("dotnet build Source/DafnyDriver/DafnyDriver.csproj");
      log(`./Binaries/Dafny ${programArguments} \"${testFile}\"`);
      log("-------------------------------------------------------------");
      log("| Create a test configuration in Rider:                     |");
      log(`Name:  git-issue-${issueNumber}-${issueKeyword}`);
      log("Project:   Dafny");
      log("Framework: net6.0");
      log(`Exe path:  ${process.cwd()}/Binaries/Dafny.exe`);
      log(`Arguments: ${programArguments} "${testFile}"`);
      log("Directory: "+process.cwd());
      log("-------------------------------------------------------------");
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
      await this.recoverData();
      var issueNumber = this.issueNumber;
      var addedTestCasesString = this.addedTestCases.map(t => "|DisplayName~" + t).join("")
      
      return `dotnet test -v:n Source/IntegrationTests/IntegrationTests.csproj`+
      ` --filter "DisplayName~git-issues/git-issue-${issueNumber}${addedTestCasesString}"`;
    },
    // Adds one more existing test to the branch by adding it in an empty commit.
    async addExisting(issueHint) {
      var testName = issueHint;
      // List all the files in TEST_FOLDER that contain "testName", which might contain a directory separator
      var testFiles = await execLog(`find ${TEST_FOLDER} -name "*.dfy"`, "Listing all the test files that contain "+testName);
      testFiles = testFiles.stdout.split("\n").map(file => file.trim());
      // Remove TEST_FOLDER from the prefix of each file
      testFiles = testFiles.map(file => file.substring(TEST_FOLDER.length));
      var testFile = testFiles.filter(file => file.indexOf(testName) >= 0);
      if(testFile.length == 0) {
        log("Could not find the test file for "+testName);
        while(testFile.length == 0 && testName.length > 0) {
          testName = testName.substring(0, testName.length - 1);
          testFile = testFiles.filter(file => file.indexOf(testName) >= 0);
          if(testFile.length > 0) {
            log("A prefix of your entry matched some files: '"+testName+"':");
            log(testFile);
            log("Re-run to confirm if it's the right file.");
          }
        }
        return false;
      }
      log(`The following test file${testFile.length > 1 ? "s" : ""} will be added:`);
      for(var file of testFile) {
        log(file);
      }
      if(!ok(await question(`Confirm? ${ACCEPT_HINT}`))) {
        return false;
      }
      var commitMessage = `${this.commitPrefix}:${testFile.join(" ")}`;
      await execLog(`git commit --only --allow-empty -m "${commitMessage}"`, "Adding the tests files...");
      return true;
    }
  };
}

function getLanguageServerDiagnosticTestManager(issueNumber, issueKeyword, name = "") {
  const testTemplate = (methodName, content) => `[Fact]
    public async Task ${methodName}() {
      var source = @"
${content.replace(/"/g,"\"\"")}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      // Uncomment what you need.
      // var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      // Assert.Equal(1, diagnostics.Length);
      // ApplyChange(ref documentItem, ((0, 0), (3, 0)), "insert text");
      // diagnostics = await GetLastDiagnostics(documentItem, CancellationToken); // If expect no parsing error
      // diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken); // If expect parsing errors
      // Assert.Equal(0, diagnostics.Length);
      
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }
    
    `;
  return getLanguageServerManager("Diagnostics/DiagnosticsTest.cs", testTemplate, issueNumber, issueKeyword, name);
}

function getLanguageServerGutterIconsManager(issueNumber, issueKeyword, name = "") {
  const testTemplate = (methodName, content) => `[Fact]
  public async Task ${methodName}() {
    await VerifyTrace(@"
${content.replace(/"/g,"\"\"")}", false, intermediates: false);
  }
 
  `;
  return getLanguageServerManager("GutterStatus/SimpleLinearVerificationGutterStatusTester.cs", testTemplate, issueNumber, issueKeyword, name);
}

function DashToCamlCase(name) {
  return name.replace(/^\w|-+(\w)/g, match => match.length == 1 ? match.toUpperCase() : match[1].toUpperCase());
}

function getLanguageServerManager(fileName, testTemplate, issueNumber, issueKeyword, name = "") {
  if(name == "") {
    name = DashToCamlCase(issueKeyword);
  }
  return {
    type: "language-server at "+fileName,
    shortName: `Test named 'GitIssue${issueNumber}${name}' in DafnyLanguageServer.Test/${fileName}`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
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
        log("Could not find " + this.testFile);
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
      var firstTestMatch = /\[Fact\]/.exec(this.testFileContent);
      if(!firstTestMatch) {
        log(`Could not find [Fact] in ${this.testFile}`);
        throw ABORTED;
      }
      var i = firstTestMatch.index;
      this.MethodName = "GitIssue" + this.issueNumber + this.name;
      if(this.testFileContent.indexOf(this.MethodName) >= 0) {
        this.MethodName = FindAppropriateSuffix(this.testFileContent, "GitIssue" + this.issueNumber + this.Name)
      }
      var newTestFileContent = this.testFileContent.substring(0, i) + testTemplate(this.MethodName, content)+this.testFileContent.substring(i);

      log(`Going to add test ${this.MethodName} in ${this.testFile}...`);
      await fs.promises.writeFile(this.testFile, newTestFileContent);
    },
    async openAndYield() {
      openAndYield(this.testFile);
      log("Look for "+this.MethodName+"! It should be the first test.");
    },
    async displayXunitTestCmd() {
      log((await this.xunitTestCmd()).replace(/Test --filter/g, "Test \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      await this.recoverData();
      log("-------------------------------------------------------------");
      log("| Ensure you put the path of the language server for VSCode:|");
      log(`Dafny: Language Server Runtime Path:\n${process.cwd()}/Binaries/Dafny.exe`);
      log("-------------------------------------------------------------");
      log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd()
      log("-------------------------------------------------------------");
      log("| Run the test in Rider:                                    |");
      log(this.MethodName);
      log("-------------------------------------------------------------");
    },
    patternsToAddToGit() {
      return [ this.testFile ];
    },
    async addToGit() {
      await addAll(this.patternsToAddToGit(), fileName);
    },
    async xunitTestCmd() {
      return `dotnet test --nologo Source/DafnyLanguageServer.Test --filter ${this.rawMethodName()}`;
    },
    async addExisting(issueHint) {
      log("TODO: Need ability to add existing language server tests");
      return false;
    }
  };
}

async function recoverTests(testManager, issueNumber) {
  if(!testManager.testFileContent && fs.existsSync(testManager.testFile)) {
    testManager.testFileContent = await fs.promises.readFile(testManager.testFile, "utf-8");
  }
  if(!testManager.testFileContent) {
    //log("Could not find " + this.testFile);
    testManager.existingTests = [];
    return;
  }
  if(testManager.existingTests == null) {
    testManager.existingTests = [];
    testManager.regex.lastIndex = 0;
    while(match = testManager.regex.exec(testManager.testFileContent)) {
      if(match[2] == issueNumber + "") {
        testManager.existingTests.push(match[1]);
      }
    }
  }
  testManager.MethodName = testManager.existingTests[0]; // Might be null
  testManager.MethodName = testManager.rawMethodName();
}

function getFormatterManager(issueNumber, issueKeyword, name = "") {
  if(name == "") {
    name = DashToCamlCase(issueKeyword);
  }
  var fileName = "FormatterIssues.cs";
  const testTemplate = (methodName, content) => `[Fact]
    public void ${methodName}() {
      FormatterWorksFor(@"
${content.replace(/"/g,"\"\"")}");
    }
    
    `;
  return {
    type: "formatter",
    shortName: `Test named 'GitIssue${issueNumber}${name}' in DafnyPipeline.Test/${fileName}`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
    testFile: `Source/DafnyPipeline.Test/${fileName}`,
    testFileContent: null,
    regex: /public\s+void\s+(GitIssue(\d+)\w+)\(\)\s*\{/g,
    existingTests: null,
    name: name,
    async recoverData() {
      await recoverTests(this, this.issueNumber);
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
      var firstTestMatch = /\[Fact\]/.exec(this.testFileContent);
      if(!firstTestMatch) {
        log(`Could not find [Fact] in ${this.testFile}`);
        throw ABORTED;
      }
      var i = firstTestMatch.index;
      this.MethodName = "GitIssue" + this.issueNumber + this.name;
      if(this.testFileContent.indexOf(this.MethodName) >= 0) {
        this.MethodName = FindAppropriateSuffix(this.testFileContent, this.MethodName);
      }
      var newTestFileContent = this.testFileContent.substring(0, i) +
        testTemplate(this.MethodName, content)+this.testFileContent.substring(i);

      log(`Going to add test ${this.MethodName} in ${this.testFile}...`);
      await fs.promises.writeFile(this.testFile, newTestFileContent);
    },
    async openAndYield() {
      openAndYield(this.testFile);
      log("Look for "+this.MethodName+"! It should be the first test.");
    },
    async displayXunitTestCmd() {
      log((await this.xunitTestCmd()).replace(/Test --filter/g, "Test \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      await this.recoverData();
      log("-------------------------------------------------------------");
      log("| Ensure you put the path of the language server for VSCode:|");
      log(`Dafny: Language Server Runtime Path:\n${process.cwd()}/Binaries/Dafny.exe`);
      log("-------------------------------------------------------------");
      log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd()
      log("-------------------------------------------------------------");
      log("| Run the test in Rider:                                    |");
      log(this.MethodName);
      log("-------------------------------------------------------------");
    },
    patternsToAddToGit() {
      return [ this.testFile ];
    },
    async addToGit() {
      await addAll(this.patternsToAddToGit(), fileName);
    },
    async xunitTestCmd() {
      return `dotnet test --nologo Source/DafnyPipeline.Test --filter ${this.rawMethodName()}`;
    },
    async addExisting(issueHint) {
      log("TODO: Need ability to add existing formatter tests");
      return false;
    }
  };
}


function getTestGenerationManager(issueNumber, issueKeyword, name = "") {
  if(name == "") {
    name = DashToCamlCase(issueKeyword);
  }
  var fileName = "Various.cs";
  /*const testTemplate = (methodName, content) => `[Fact]
    public void ${methodName}() {
      FormatterWorksFor(@"
${content.replace(/"/g,"\"\"")}");
    }
    
    `;*/
  return {
    type: "test generation",
    shortName: `Test named 'GitIssue${issueNumber}${name}' in DafnyTestGeneration.Test/${fileName}`,
    issueNumber: issueNumber,
    issueKeyword: issueKeyword,
    commitPrefix: "FIXER-TEST-GENERATION",
    testFile: `Source/DafnyTestGeneration.Test/${fileName}`,
    testFileContent: null,
    regex: /public\s+async\s+Task\s+(GitIssue(\d+)\w+)\(\)\s*\{/g,
    existingTests: null, // Existing tests for this issue number
    addedTests: null, // Other tests
    name: name,
    async recoverData() {
      await recoverTests(this, this.issueNumber);
      this.addedTests = await getAllAddedTestsWithPrefix(this.commitPrefix, false);
    },
    rawMethodName() {
      // Remove any letter suffix so that we have a pattern that can cover all similar issues
      return this.MethodName != null ? this.MethodName.replace(/[A-Z]$/, "") : null;
    },
    async exists() {
      await this.recoverData();
      return this.existingTests.length > 0 || this.addedTests && this.addedTests.length > 0;
    },
    async create(content) {
      log("Cannot create test generation yet");
      throw ABORTED;
    },
    async openAndYield() {
      return false; // TODO
      //openAndYield(this.testFile);
      //log("Look for "+this.MethodName+"! It should be the first test.");
    },
    async displayXunitTestCmd() {
      log((await this.xunitTestCmd()).replace(/Test --filter/g, "Test \\\n--filter").replace(/\|/g, "|\\\n"));
    },
    async displayRunHelp() {
      await this.recoverData();
      log("-------------------------------------------------------------");
      log("| Run the test as part of the XUnit test:                   |");
      this.displayXunitTestCmd()
      log("-------------------------------------------------------------");
      log("| Run the test in DafnyTestGeneration.Test in Rider:        |");
      log(this.MethodName);
      log("-------------------------------------------------------------");
    },
    patternsToAddToGit() {
      return [ this.testFile ];
    },
    async addToGit() {
      await addAll(this.patternsToAddToGit(), fileName);
    },
    async xunitTestCmd() {
      var addedTestsCmd = this.addedTests.join("|");
      return `dotnet test --nologo Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --filter ${addedTestsCmd}`;
    },
    async addExisting(issueHint) {
      // Find all lines `async\s+Task\s+(...issueHint...)\s*` in any .cs file inside Source/DafnyTestGeneration.Test
      // Display entire lines, NOT the file names
      var testFiles = await execLog("git ls-files Source/DafnyTestGeneration.Test/*.cs", "Searching for test files...");
      if(testFiles.stderr || !testFiles.stdout) {
        log(testFiles.stderr);
        return false;
      }
      var csFiles = testFiles.stdout;
      var regex = new RegExp("async\\s+Task\\s+(.*"+issueHint+"[^\\(]*)", "g");
      var fullMethodNames = []; // array of [file, method];

      for(var csFile of csFiles.split("\n").filter(x => x.length > 0)) {
        var fileContent = await fs.promises.readFile(csFile, 'utf-8');
        var match = regex.exec(fileContent);
        if(match) {
          var methodName = match[1];
          fullMethodNames.push([csFile, methodName]);
        }
      }
      if(fullMethodNames.length == 0) {
        return false;
      }

      log(`The following test generation test${fullMethodNames.length > 1 ? "s" : ""} will be added:`);
      for(var [csFile, methodName] of fullMethodNames) {
        log(`  ${methodName}()  (from ${csFile})`);
      }
      if(!ok(await question(`Confirm? ${ACCEPT_HINT}`))) {
        return false;
      }
      var fullMethodNamesString = fullMethodNames.map(x => x[1]).join(",");
      var commitMessage = `${this.commitPrefix}:${fullMethodNamesString}`;
      await execLog(`git commit --only --allow-empty -m "${commitMessage}"`, "Adding the test generation tests files...");
      return true;
    }
  };
}

function FindAppropriateSuffix(fileContent, baseName) {
  var suffix = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  var indexSuffix = 0;
  while(indexSuffix < suffix.length && fileContent.indexOf(baseName + suffix[indexSuffix]) >= 0) {
    indexSuffix++;
  }
  if(indexSuffix >= suffix.length) {
    log("Too many test files prefixed by "+baseName);
    throw ABORTED;
  }
  return baseName + suffix[indexSuffix];
}

function getIntegrationTestFileName(issueNumber, suffix = "") {
  return `${TEST_FOLDER}git-issues/git-issue-${issueNumber}${suffix}.dfy`;
}
function getIntegrationTestFileExpectName(issueNumber, suffix = "") {
  return getIntegrationTestFileName(issueNumber, suffix)+".expect";
}
// Process `fix more` with the given detected issueNumber, and moreText is the argument after "more".
async function doAddExistingOrNewTest(testManagers, moreText) {
  var otherIssueNumber = moreText || await question("Please enter either\n-Another existing issue number from which to import tests\n-The name of an existing integration test\n-Blank if you want to create a new test manually\n");
  if(otherIssueNumber != "" && !otherIssueNumber.match(/^\d+$/)) {
    for(let k in testManagers) {
      var testManager = testManagers[k];
      if(await testManager.addExisting(otherIssueNumber)) {
        return;
      }
    }    
  }

  // Let's create a new test.
  var {programReproducingError, test_type} =
    await interactivelyCreateTestFileContent(otherIssueNumber);
  if(test_type == TEST_TYPE.SKIP_TEST_CREATION) {
    throw ABORTED;
  }
  await testManagers[test_type].create(programReproducingError);
  await testManagers[test_type].openAndYield();
}

// We will want to run tests on the language server at some point
// (DafnyLanguageServer/Diagnostics/DiagnosticsTest.cs).

// The main function
async function Main() {
  if(typeof testing == "boolean" && testing) {
    return;
  }
  var {openFiles, skipVerification, addOneTestCase, args, defaultMessage, run, unitTests} = processArgs();
  var fixBranchDidExist = false;
  var testFileContent = "";
  var providedIssueNumber = args[2];
  var providedKeywordNumber = args[3];
  var providedContent = args[4]; // Should deprecate. No one is ever going to add a test content as an argument of the command line.
  var returnedException = null;
  try {
    if(unitTests) {
      if(typeof runUnitTests == "function") {
        await runUnitTests();
        rl.close();
        throw FINISHED;
      } else {
        console.log("Please run test/fix-dafny-issue-tests.js")
      }
    }
    if(run) {
      if(providedIssueNumber == null) {
        log("Usage: fix run <integration test name>");
        return;
      }
      var testCmd = `dotnet test -v:n Source/IntegrationTests/IntegrationTests.csproj\\\n`+
    ` --filter "DisplayName~${providedIssueNumber}"`;
      log("You can run the following command:\n"+ testCmd);
      return;
    }
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
    var testInfoFormatter = getFormatterManager(issueNumber, issueKeyword);
    var testManagers = {
      [TEST_TYPE.INTEGRATION] : testInfo,
      [TEST_TYPE.LANGUAGE_SERVER] : testInfoLSDiagnostic,
      [TEST_TYPE.LANGUAGE_SERVER_ICONS] : testInfoLSIcons,
      [TEST_TYPE.FORMATTER] : testInfoFormatter,
      [TEST_TYPE.TEST_GENERATION]: getTestGenerationManager(issueNumber, issueKeyword)
    };
    var testFilesDidExist = addOneTestCase;
    for(let i in testManagers) {
      testFilesDidExist = testFilesDidExist || await testManagers[i].exists();
    }
    if(!testFilesDidExist) {
      if(fixBranchDidExist) {
        log("You still haven't set up any test for your branch.");
      }
      addOneTestCase = false; // This will be automatic
      var {programReproducingError: testFileContent, test_type} =
        await interactivelyCreateTestFileContent(issueNumber, providedContent);
      if(test_type != TEST_TYPE.SKIP_TEST_CREATION) {
        testManagers[test_type].create(testFileContent);
      }
    }
    var testsNowExist = testFilesDidExist || test_type != TEST_TYPE.SKIP_TEST_CREATION;
    if(addOneTestCase) {
      await doAddExistingOrNewTest(testManagers, providedIssueNumber);
    }

    if(test_type != TEST_TYPE.SKIP_TEST_CREATION && (!fixBranchDidExist || openFiles || neededToSwitchToExistingBranch)) {
      for(let k in testManagers) {
        var testManager = testManagers[k];
        if(await testManager.exists()) {
          await testManager.openAndYield();
        }
      }
    }
    if(neededToSwitchToExistingBranch) {
      skipVerification = false;
      if(ok(await question(`You switched branches. Rebuild solution now? (ENTER or y for yes)`)) ){
        neededToSwitchToExistingBranch = !ok(await question(`Ok, will rebuild. Do you want to reverify tests afterwards? (ENTER or y for yes)`));
        await buildSolution(issueNumber);
      } else {
        neededToSwitchToExistingBranch = true;
      }
    }

    if(!fixBranchDidExist) {
      await createBranchAndAddTestFiles(testManagers, branchName, test_type == TEST_TYPE.SKIP_TEST_CREATION);
    }
    if(testsNowExist) {
      for(let k in testManagers) {
        var testManager = testManagers[k];
        if(await testManager.exists()) {
          await testManager.displayRunHelp();
        }
      }
    }
    if((!fixBranchDidExist || !testFilesDidExist || openFiles) &&
        (!skipVerification || test_type != TEST_TYPE.SKIP_TEST_CREATION)) {
      var withoutOpen = open ? " (without 'open')" : "";
      if(fixBranchDidExist && !testFilesDidExist) {
        log("You don't have any tests set. You can force push your changes using 'fix force'");
      } else {
        log(`All set! Now focus on making the tests to pass. You can add additional tests by typing 'fix more'`);
        log(`When the tests succeed, re-run this script to verify the fix and create the PR.\nYou can run the same command-line${withoutOpen}.`);
      }
    } else {
      var testResult = {};
      if(skipVerification || !neededToSwitchToExistingBranch && ((
           testResult = await verifyFix(testManagers), testResult.ok))) {
        var wasPushed = await originAlreadyExists(branchName);
        if(skipVerification) {
          log(`You indicated "force", so you assume that this commit solves the issue #${issueNumber}.`);
        } else {
          log(`\nCongratulations for ${wasPushed ? "ensuring this new commit still solves" : "solving"} issue #${issueNumber}!`);
        }

        if(!wasPushed && defaultMessage == null && !ok(await question("Are you ready to create the PR? " + ACCEPT_HINT))) {
          throw ABORTED;
        }
        var commitMessage = "";
        if(!wasPushed) {
          if(defaultMessage != null) {
            // defaultMessage is either a "Fix: ..." or "Feat: ..." so we need to extract them. If not, error.
            var [extension, releaseNotesLine] = defaultMessage.split(":");
            releaseNotesLine = releaseNotesLine.trim();
            extension = extension.toLowerCase();
            if(extension != "fix" && extension != "feat") {
              log("The default message must start with 'Fix:' or 'Feat:'");
              var {releaseNotesLine, extension} = await getReleaseNotesLine(issueNumber);
            }
          } else {
            var {releaseNotesLine, extension} = await getReleaseNotesLine(issueNumber);
          }
          await addTownCrierEntry(issueNumber, releaseNotesLine, extension);
          var prContent = `This PR fixes #${issueNumber}\nI added the corresponding test.\n\n<small>By submitting this pull request, I confirm that my contribution is made under the terms of the [MIT license](https://github.com/dafny-lang/dafny/blob/master/LICENSE.txt).</small>`;
          commitMessage = `${(extension == "fix" ? "Fix" : "Feat")}: ${releaseNotesLine}`;
        } else {
          commitMessage = defaultMessage ?? await question("What should be the commit message?\n");
        }
        await commitAllAndPush(testInfo, commitMessage, branchName, testsNowExist);
        if(!wasPushed) {
          var url = `https://github.com/dafny-lang/dafny/compare/${branchName}?expand=1&title=`+encodeURIComponent(commitMessage)+"&body="+encodeURIComponent(prContent);
          log("Opening the browser to create a PR at this URL...:\n"+url);
          await open(url);
          log("Look at your browser, it should be opened.");
        } else {
          log("Updated the PR.");
        }
      } else {
        if(neededToSwitchToExistingBranch && testResult.ok) {
          log("The tests are passing as expected. Run 'fix' when you have something new to verify.\n");
        } else {
          log(testResult.log);
          log("The test did not pass. Please fix the issue and re-run this script after ensuring that the following command-line succeeds:\n");
          // Print special characters to stdout so that it notifies the user (bell?)
          process.stdout.write("\x07");
          for(let k in testManagers) {
            var testManager = testManagers[k];
            if(await testManager.exists()) {
              testManager.displayXunitTestCmd();
            }
          }
          await helpIfDllLock(testResult.log);
        }
      }
    }
  } catch(e) {
    returnedException = e;
    if(e !== FINISHED && e !== ABORTED) {
      console.log(e);
      throw e;
    }
  } finally {
    rl.close();
    if(returnedException != FINISHED && returnedException !== null) {
      exit(1);
    } else {
      exit(0);
    }
  }
}