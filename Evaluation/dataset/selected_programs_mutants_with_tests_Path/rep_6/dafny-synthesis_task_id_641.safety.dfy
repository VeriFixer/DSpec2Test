method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test5() {
expect 739 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(739);
expect r0 == 739 * (7 * 739 - 5) / 2;
}

// REPEAT 6 - TIME: 8.5399188 s
