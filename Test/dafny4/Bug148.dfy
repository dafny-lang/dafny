// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
    var zero    : real  := 0.0;
		var three   : real  := 3.0;
    var fifteen : real  := 15.0;
		var negone  : real  := -1.0;
		var negthree : real := -3.0;

		print zero <= fifteen, "\n";  // true
		print fifteen <= zero, "\n";  // false
		print negone <= zero, "\n";   // true
		print zero <= negone, "\n";   // false
		print negone <= fifteen, "\n"; // true
		print fifteen <= negone, "\n";  // false

		print zero >= fifteen, "\n";  // false
		print fifteen >= zero, "\n";  // true
		print negone >= zero, "\n";   // false
		print zero >= negone, "\n";   // true
		print negone >= fifteen, "\n"; // false
		print fifteen >= negone, "\n";  // true
}
