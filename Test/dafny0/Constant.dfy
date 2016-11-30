// RUN: %dafny /compile:3  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const one:int := 1
const two:int := one * 2
const three:int := one + two
const Pi:real := 3.14

class Calendar {
  const months:int := 12
  const weeks:int := 52
}

method Main() {
	print "one := ", one, "\n";
	print "two := ", two, "\n";
	print "three := ", three, "\n";
	assert three == 3;
	print "Pi := ", Pi, "\n";
	assert Pi == 3.14;
	var weeks := Calendar.weeks;
	print "months := ", Calendar.months, "\n";
	print "weeks := ", weeks, "\n";
	assert weeks == 52;
}
