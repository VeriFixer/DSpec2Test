method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
}

method {:test} Test12() {
expect 163555288339858862 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(163555288339858862);
expect r0 == 163555288339858862 * (7 * 163555288339858862 - 5) / 2;
}

// REPEAT 8 - TIME: 40.4077421 s
