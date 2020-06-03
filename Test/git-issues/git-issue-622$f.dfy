// RUN: rm -f 'git-issue-622$f/git_issue_622$f.java'
// RUN: %dafny /compile:3 /compileTarget:java /spillTargetCode:3 "%s" > "%t"
// RUN: file 'git-issue-622$f/git_issue_622$f.java' >> "%t"
// RUN: %diff "%s.expect" "%t"

class fg {

static method Main() {
}

}
