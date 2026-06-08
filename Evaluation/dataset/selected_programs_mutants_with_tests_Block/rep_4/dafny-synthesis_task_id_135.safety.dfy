method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
{
    hexNum := n * ((2 * n) - 1);
}

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(3);
expect r0 == 3 * (2 * 3 - 1);
}

// REPEAT 4 - TIME: 4.0890375 s
