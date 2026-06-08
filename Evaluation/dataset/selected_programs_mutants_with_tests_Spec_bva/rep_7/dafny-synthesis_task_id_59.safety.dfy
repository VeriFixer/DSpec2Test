method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
{
    octagonalNumber := n * (3 * n - 2);
}

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(106);
expect r0 == 106 * (3 * 106 - 2);
}

// REPEAT 7 - TIME: 10.4043132 s
