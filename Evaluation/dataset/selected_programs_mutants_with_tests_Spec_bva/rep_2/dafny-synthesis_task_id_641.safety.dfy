method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(101);
expect r0 == 101 * (7 * 101 - 5) / 2;
}

// REPEAT 2 - TIME: 35.8487237 s
