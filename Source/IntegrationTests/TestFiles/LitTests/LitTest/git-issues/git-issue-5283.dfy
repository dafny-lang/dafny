// RUN: %testDafnyForEachCompiler "%s"

/* Obtained from
https://pkg.go.dev/std
by running on the console
copy([...document.querySelectorAll(
    "td > div.UnitDirectories-pathCell > div > span, "+
    "td > div.UnitDirectories-pathCell > div > a")]
    .map(e => "module " + e.textContent + " {}").join("\n"))
*/
module archive {}
module bufio {}
module builtin {}
module bytes {}
module cmp {}
module compress {}
module container {}
module context {}
module crypto {}
module database {}
module debug {}
module embed {}
module encoding {}
module errors {}
module expvar {}
module flag {}
module fmt {}
module go {}
module hash {}
module html {}
module image {}
module index {}
module internal {}
module io {}
module log {}
module maps {}
module math {}
module mime {}
module net {}
module os {}
module path {}
module plugin {}
module reflect {}
module regexp {}
module runtime {}
module slices {}
module sort {}
module strconv {}
module strings {}
module sync {}
module syscall {}
module testing {}
module text {}
module time {}
module unicode {}
module unsafe {}

method Main(){
    print "done\n";
}