method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
{
    hexNum := n * ((2 * n) - 1);
}

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(107);
expect r0 == 107 * (2 * 107 - 1);
}

// REPEAT 8 - TIME: 11.4386485 s
