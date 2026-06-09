
method {:test} Test13() {
expect 37450465281508189576483680376842269 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842269);
expect r0 == 37450465281508189576483680376842269 * (7 * 37450465281508189576483680376842269 - 5) / 2;
}

// REPEAT 9 - TIME: 42.9378584 s