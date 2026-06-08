method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
{
    octagonalNumber := n * (3 * n - 2);
}

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(107);
expect r0 == 107 * (3 * 107 - 2);
}

// REPEAT 8 - TIME: 11.0647819 s
