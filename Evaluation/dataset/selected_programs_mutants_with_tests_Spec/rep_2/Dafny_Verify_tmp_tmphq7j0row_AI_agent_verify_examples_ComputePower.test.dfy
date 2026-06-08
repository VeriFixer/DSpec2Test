
method {:test} Test1() {
expect 2440 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2440);
expect r0 == Power(2440);
}

// REPEAT 2 - TIME: 4.2934866 s