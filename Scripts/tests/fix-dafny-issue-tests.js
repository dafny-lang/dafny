#!/usr/bin/env node

var testing = true;
// Import the file fix-dafny-issue.js
var fileToTest = require("fs").readFileSync("../fix-dafny-issue.js", "utf8");
eval(fileToTest);

runUnitTests();

//////// Testing tools

function assertEqual(got, expected, reportLevel = 1) {
  if(got != expected) {
    let trace = (new Error()).stack;
    let r = require("path").basename(__filename) + ":(\\d+):(\\d+)";
    let regex = new RegExp(r, "g");
    let lines = [];
    let m;
    while(m = regex.exec(trace)) {
      lines.push(m[1]);
    }
    // The first one is in this function so we remove it
    lines.shift();
    console.log("Line " + lines[0] + ", expected " + JSON.stringify(expected) + " but got " + JSON.stringify(got));
    lines.shift();
    while(lines.length > 0) {
      console.log("See line " + lines[0]);
      lines.shift();
    }
    throw constants.ABORTED;
  }
}

async function runUnitTests() {
  var returnedException = null;
  try {
    testHasLabel();
    testExtractProgram();
    await testInteractivelyCreateTestFileContent();
    console.log("All tests are successful");
  } catch(e) {
    returnedException = e;
    console.log(e);
    throw e;
  } finally {
    if(returnedException !== null) {
      process.exit(1);
    } else {
      process.exit(0);
    }
  }
}

function testHasLabel() {
  assertEqual(hasLabel({labels: [{name: "language-server"}]}, "language-server"), true);
  assertEqual(hasLabel({labels: [{name: "language-server"}]}, "formatter"), false);
  assertEqual(hasLabel({labels: [{name: "language-server"}, {name: "formatter"}]}, "formatter"), true);
  assertEqual(hasLabel({labels: [{name: "language-server"}, {name: "formatter"}]}, "language-server"), true);
  assertEqual(hasLabel({labels: [{name: "language-server"}, {name: "formatter"}]}, "language-server-icons"), false);
  assertEqual(hasLabel({labels: [{name: "language-server"}, {name: "formatter"}]}, "language-server-icons"), false);
}

function testExtractProgram() {
  assertEqual(extractProgram({}), ""),
  assertEqual(extractProgram({body: "I have an issue and Dafny does not compile. What should I do?"}), "");
  assertEqual(extractProgram({body: "Here is the program causing me pain:\n```dafny\nclass C {\n  static int f() {\n    return 1;\n  }\n}\n```\n Can you please help?"}),
    "class C {\n  static int f() {\n    return 1;\n  }\n}");
  assertEqual(extractProgram({body: "Here is the program causing me pain:\n```  dafny\nclass C {\n  static int f() {\n    return 1;\n  }\n}\n```\n Can you please help?"}),
    "class C {\n  static int f() {\n    return 1;\n  }\n}");
}


async function RunQuestions(issue_number, command_line_content, github_cache, questions, expected_test_type, expected_program, expected_log) {
  var savedQuestionCache = constants.questionCache;
  var savedCache = null;
  var savedLogger = constants.logTest;
  constants.logTest = "";
  if(github_cache != null) {
    savedCache = constants.cache;
    constants.cache = {[issue_number]: github_cache};
  }
  constants.questionCache = questions;
  var {programReproducingError, test_type} = await interactivelyCreateTestFileContent(issue_number, command_line_content);
  assertEqual(test_type, expected_test_type, 2); 
  assertEqual(programReproducingError, expected_program, 2);
  assertEqual(constants.logTest, expected_log ?? "", 2);
  if(savedCache != null) {
    constants.cache = savedCache;
  }
  constants.questionCache = savedQuestionCache;
  constants.logTest = savedLogger;
}

async function testInteractivelyCreateTestFileContent() {
  await RunQuestions(null, null, null, {
["Do you want to reproduce this problem\n"+
 "- On the command line (ENTER or 1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: "1",
 ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "y",
 ["Will the test need to be run (i.e. will have a Main() method)? " + constants.ACCEPT_HINT]: "Yep"},
 constants.TEST_TYPE.INTEGRATION,
    `// RUN: %testDafnyForEachCompiler "%s"\n\nmethod Main() {\n  \n}`,
  "All backends are going to be tested. If you want to modify the output "+
  "of a particular backend or ignore one, please check "+
  "Source/IntegrationTests/TestFiles/LitTests/LitTest/README.md.");

  await RunQuestions("42", null, {
    body: "Here is the program I can't run:\n```dafny\nmethod Main() {print a; }\n```\n Can you please help?"
  }, {
    ["Do you want to reproduce this problem\n"+
     "- On the command line (ENTER or 1)\n"+
     "- A diagnostic test on the language server(2)\n"+
     "- A formatter test (3)\n"+
     "- A gutter icons test on the language server (4)\n"+
    "- Don't create test files(5)?\n"+
     "> "]: "1",
     ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "y"
       // Detection of Main() method, so it will be run without asking question
    },
     constants.TEST_TYPE.INTEGRATION,
     "// RUN: %testDafnyForEachCompiler \"%s\"\n\nmethod Main() {print a; }",
     "All backends are going to be tested. If you want to modify the output "+
     "of a particular backend or ignore one, please check "+
     "Source/IntegrationTests/TestFiles/LitTests/LitTest/README.md.");
    
  await RunQuestions(null, null, null, {
["Do you want to reproduce this problem\n"+
 "- On the command line (ENTER or 1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: "1",
 ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "y",
 ["Will the test need to be run (i.e. will have a Main() method)? " + constants.ACCEPT_HINT]: "n"},
 constants.TEST_TYPE.INTEGRATION,
 "// RUN: %baredafny verify %args \"%s\" > \"%t\"\n// RUN: %baredafny build %args --no-verify -t:cs \"%s\" >> \"%t\"\n// RUN: %baredafny build %args --no-verify -t:js \"%s\" >> \"%t\"\n// RUN: %baredafny build %args --no-verify -t:cpp \"%s\" >> \"%t\"\n// RUN: %baredafny build %args --no-verify -t:java \"%s\" >> \"%t\"\n// RUN: %baredafny build %args --no-verify -t:go \"%s\" >> \"%t\"\n// RUN: %baredafny build %args --no-verify -t:py \"%s\" >> \"%t\"\n// RUN: %diff \"%s.expect\" \"%t\"\n\n",
 "All backends are going to be tested. If you want to modify the output "+
 "of a particular backend or ignore one, please check "+
 "Source/IntegrationTests/TestFiles/LitTests/LitTest/README.md.");

  await RunQuestions(null, null, null, {
["Do you want to reproduce this problem\n"+
 "- On the command line (ENTER or 1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: "1",
 ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "n",
 ["Will the test eventually pass verification? " + constants.ACCEPT_HINT]: "Yep"},
 constants.TEST_TYPE.INTEGRATION,
 `// RUN: %baredafny verify %args "%s" > "%t"\n// RUN: %diff "%s.expect" "%t"\n\n`,
  null);

  await RunQuestions(null, null, null, {
["Do you want to reproduce this problem\n"+
 "- On the command line (ENTER or 1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: "1",
 ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "n",
 ["Will the test eventually pass verification? " + constants.ACCEPT_HINT]: "nope",
 ["Will the test eventually pass resolution? " + constants.ACCEPT_HINT]: "yohoo"},
 constants.TEST_TYPE.INTEGRATION,
 "// RUN: %exits-with 4 %baredafny verify %args \"%s\" > \"%t\"\n// RUN: %diff \"%s.expect\" \"%t\"\n\n",
  null);

  await RunQuestions(null, null, null, {
["Do you want to reproduce this problem\n"+
 "- On the command line (ENTER or 1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: "1",
 ["Will the test need to be compiled? " + constants.ACCEPT_HINT]: "n",
 ["Will the test eventually pass verification? " + constants.ACCEPT_HINT]: "nope",
 ["Will the test eventually pass resolution? " + constants.ACCEPT_HINT]: "N"},
 constants.TEST_TYPE.INTEGRATION,
 "// RUN: %exits-with 2 %baredafny verify %args \"%s\" > \"%t\"\n// RUN: %diff \"%s.expect\" \"%t\"\n\n",
  null);

  // Test with fetching github issue
  await RunQuestions("42", null, {
    labels: [{name: "language-server"}],
    body: "Here is the program crashing the language server:\n```dafny\nclass C {\n  static int f() {\n    return 1;\n  }\n}\n```\n Can you please help?"
  }, {
["Do you want to reproduce this problem\n"+
 "- On the command line (1)\n"+
 "- A diagnostic test on the language server(ENTER or 2)\n"+ // Default is 2 now
 "- A formatter test (3)\n"+
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: ""},
 constants.TEST_TYPE.LANGUAGE_SERVER,
 "class C {\n  static int f() {\n    return 1;\n  }\n}",
  null);

  await RunQuestions("42", null, {
    labels: [{name: "formatter"}],
    body: "Here is the program crashing the formatter:\n```dafny\nclass C {\n  static int f() {\n    return 1;\n  }\n}\n```\n Can you please help?"
  }, {
["Do you want to reproduce this problem\n"+
 "- On the command line (1)\n"+
 "- A diagnostic test on the language server(2)\n"+
 "- A formatter test (ENTER or 3)\n"+ // Default is 3 now
 "- A gutter icons test on the language server (4)\n"+
"- Don't create test files(5)?\n"+
 "> "]: ""},
 constants.TEST_TYPE.FORMATTER,
 "class C {\n  static int f() {\n    return 1;\n  }\n}",
  null);
}
