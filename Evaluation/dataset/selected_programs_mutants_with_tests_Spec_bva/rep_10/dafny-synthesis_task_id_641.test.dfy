
method {:test} Test14() {
expect 37450465281508189576483680376842270 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842270);
expect r0 == 37450465281508189576483680376842270 * (7 * 37450465281508189576483680376842270 - 5) / 2;
}

// REPEAT 10 - TIME: 44.2496825 s