method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
{
    hexNum := n * ((2 * n) - 1);
}

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(108);
expect r0 == 108 * (2 * 108 - 1);
}

// REPEAT 9 - TIME: 12.0641634 s
