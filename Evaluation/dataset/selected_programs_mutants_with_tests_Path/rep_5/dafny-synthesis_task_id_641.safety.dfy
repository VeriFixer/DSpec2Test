method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test4() {
expect 738 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(738);
expect r0 == 738 * (7 * 738 - 5) / 2;
}

// REPEAT 5 - TIME: 7.4872064 s
