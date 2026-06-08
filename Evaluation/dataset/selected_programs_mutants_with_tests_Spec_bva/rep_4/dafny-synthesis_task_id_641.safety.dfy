method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(103);
expect r0 == 103 * (7 * 103 - 5) / 2;
}

// REPEAT 4 - TIME: 37.2954797 s
