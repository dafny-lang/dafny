import opened Std.Wrappers

// ------ Demo for Option ----------------------------
// We use Option when we don't need to pass around a reason for the failure,
// ie when just 'None' is sufficient:

class MyMap<K(==), V> {
  var m: map<K, V>
  constructor () {
    m := map[];
  }
  function Get(k: K): Option<V>
    reads this
  {
    if k in m then Some(m[k]) else None()
  }
  method Put(k: K, v: V)
    modifies this
  {
    this.m := this.m[k := v];
  }
}

@Test
method TestMyMap() {
  var m := new MyMap<string, string>();
  m.Put("message", "Hello");
  var greeting := Greet(m);
  expect greeting == "Hello\nError: 'name' was not found\n";

  m.Put("name", "Dafny");
  greeting := Greet(m);
  expect greeting == "Hello\nDafny\n";
}

@Test
method TestGetGreetingSuccess() {
  var m := new MyMap<string, string>();
  m.Put("message", "Hello");
  m.Put("name", "Dafny");
  var greeting := GetGreeting(m);
  expect greeting == Some("Hello Dafny");
}

@Test
method TestGetGreetingFailure() {
  var m := new MyMap<string, string>();
  var greeting := GetGreeting(m);
  expect greeting == None;
}

method Greet(m: MyMap<string, string>) returns (greeting: string) {
  var o: Option<string> := m.Get("message");
  if o.Some? {
    greeting := o.value + "\n";
  } else {
    greeting := "oops\n";
  }

  var r: Result<string, string> := FindName(m);
  if r.Success? {
    greeting := greeting + r.value + "\n";
  } else {
    greeting := greeting + "Error: " + r.error + "\n";
  }
}

// Sometimes we want to go from Option to Result:
method FindName(m: MyMap<string, string>) returns (res: Result<string, string>) {
  // Will return a default error message in case of None:
  res := m.Get("name").ToResult("'name' not found");
  // We can also match on the option to write a custom error:
  match m.Get("name")
  case Some(n) => res := Success(n);
  case None => res := Failure("'name' was not found");
}

// Propagating failures using :- statements
method GetGreeting(m: MyMap<string, string>) returns (res: Option<string>) {
  var message: string :- m.Get("message");
  var nameResult := FindName(m);
  var name :- nameResult.ToOption();
  res := Some(message + " " + name);
}

@Test
method TestOptionUtilities() {
  var stringNone: Option<string> := None;

  expect Some("thing").GetOr("else") == "thing";
  expect None.GetOr("else") == "else";

  expect Some("body once told me").ToOutcome("the world is gonna roll me") == Pass;
  expect stringNone.ToOutcome("the world is gonna roll me") == Fail("the world is gonna roll me");

  var convertor := (x: Option<string>) =>
      match x
      case None => Pass
      case Some(value) => Fail("Not expected: " + value);

  expect Some("thing").Map(convertor) == Fail("Not expected: thing");
  expect None.Map(convertor) == Pass;
}

// ------ Demo for Result ----------------------------
// We use Result when we want to give a reason for the failure:

class MyFilesystem {
  var files: map<string, string>
  constructor() {
    files := map[];
  }

  // Result<()> is used to return a Result without any data
  method WriteFile(path: string, contents: string) returns (res: OutcomeResult<string>)
    modifies this
  {
    if path in files {
      files := files[path := contents];
      res := Pass'();
    } else {
      // The "Result" datatype allows us to give precise error messages
      // instead of just "None"
      res := Fail'("File not found, use 'Create' before");
    }
  }

  method CreateFile(path: string) returns (res: OutcomeResult<string>)
    modifies this
  {
    if path in files {
      res := Fail'("File already exists");
    } else {
      files := files[path := ""];
      res := Pass'();
    }
  }

  method ReadFile(path: string) returns (res: Result<string, string>) {
    if path in files {
      res := Success(files[path]);
    } else {
      res := Failure("File not found");
    }
  }
}

// Propagating failures using :- statements
method CopyFile(fs: MyFilesystem, fromPath: string, toPath: string) returns (res: Result<(), string>)
  modifies fs
{
  var contents :- fs.ReadFile(fromPath);
  :- fs.CreateFile(toPath);
  :- fs.WriteFile(toPath, contents);
  res := Success(());
}

@Test
method TestMyFilesystem() {
  var fs := new MyFilesystem();
  :- expect fs.CreateFile("test.txt");
  :- expect fs.WriteFile("test.txt", "Test dummy file");
  var fileResult :- expect fs.ReadFile("test.txt");
  expect fileResult == "Test dummy file";

  // Testing error propagation
  var result := CopyFile(fs, "missing.txt", "newfile.txt");
  expect result == Failure("File not found");
}

@Test
method TestResultUtilities() {
  var stringSuccess: Result<string, string> := Success("I found my keys!");
  var stringFailure: Result<string, string> := Failure("I can't find my keys!");

  expect stringSuccess.GetOr("else") == "I found my keys!";
  expect stringFailure.GetOr("else") == "else";

  expect stringSuccess.ToOutcome() == Pass;
  expect stringFailure.ToOutcome() == Fail("I can't find my keys!");

  var toErrorOption := (x: Result<string, string>) =>
      match x
      case Success(_) => None
      case Failure(error) => Some(error);

  expect stringSuccess.Map(toErrorOption) == None;
  expect stringFailure.Map(toErrorOption) == Some("I can't find my keys!");

  var exaggerator := error => "ATTENTION: " + error;

  expect stringSuccess.MapFailure(exaggerator) == stringSuccess;
  expect stringFailure.MapFailure(exaggerator) == Failure("ATTENTION: I can't find my keys!");
}

// ------ Demo for Need ----------------------------
// We use Need when something has to be true but we can't prove it statically
// This is a very contrived example

method whatIsCharacterFive(fs: MyFilesystem, fromPath: string) returns (res: Result<char, string>)
  modifies fs
{

  // Get a string that we can't reason about statically
  var contents :- fs.ReadFile(fromPath);

  // Dynamically test whether the string is at least 5 characters long, and return a failure if not.
  // If we pass this line, Dafny can now assume that the string is long enough.
  :- Need<string>(|contents| >= 5, "File contents not long enough.");

  // Now we can get the character
  var c := contents[4];

  return Success(c);
}

// For a method that returns an Outcome, use Outcome.Need
method whatIsCharacterFive'(fs: MyFilesystem, fromPath: string) returns (res: Outcome<string>)
  modifies fs
{

  // Get a string that we can't reason about statically
  var result := fs.ReadFile(fromPath);
  :- result.ToOutcome();
  var contents: string := result.value;

  // Dynamically test whether the string is at least 5 characters long, and return a failure if not.
  // If we pass this line, Dafny can now assume that the string is long enough.
  :- Outcome.Need(|contents| >= 5, "File contents not long enough.");

  // Now we can get the character
  var c := contents[4];
  // and do other stuff

  return Pass;
}

@Test
method TestNeed() {
  var fs := new MyFilesystem();
  :- expect fs.CreateFile("test.txt");
  :- expect fs.WriteFile("test.txt", "12345678910");

  var c :- expect whatIsCharacterFive(fs, "test.txt");
  :- expect whatIsCharacterFive'(fs, "test.txt");

  :- expect fs.WriteFile("test.txt", "");
  var result := whatIsCharacterFive(fs, "test.txt");
  expect result.Failure? && result.error == "File contents not long enough.";
  var outcome := whatIsCharacterFive'(fs, "test.txt");
  expect outcome.Fail? && outcome.error == "File contents not long enough.";
}

@Test
method TestOutcomeUtilities() {
  var stringPass: Outcome<string> := Pass;
  var stringFail: Outcome<string> := Fail("I'm too tired");

  expect stringPass.ToOption(42) == Some(42);
  expect stringFail.ToOption(42) == None;

  expect stringPass.ToResult(42) == Success(42);
  expect stringFail.ToResult(42) == Failure("I'm too tired");

  var toErrorOption := (x: Outcome<string>) =>
      match x
      case Pass => None
      case Fail(error) => Some(error);

  expect stringPass.Map(toErrorOption) == None;
  expect stringFail.Map(toErrorOption) == Some("I'm too tired");

  var exaggerator := error => "ATTENTION: " + error;

  expect stringPass.MapFailure(exaggerator, 42) == Success(42);
  expect stringFail.MapFailure(exaggerator, 42) == Failure("ATTENTION: I'm too tired");
}