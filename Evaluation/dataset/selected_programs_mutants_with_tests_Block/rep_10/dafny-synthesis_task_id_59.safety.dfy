method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
{
    octagonalNumber := n * (3 * n - 2);
}

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(9);
expect r0 == 9 * (3 * 9 - 2);
}

// REPEAT 10 - TIME: 8.4798525 s
