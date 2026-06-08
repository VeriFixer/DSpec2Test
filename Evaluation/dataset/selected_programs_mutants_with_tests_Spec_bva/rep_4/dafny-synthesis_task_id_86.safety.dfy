method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    result := 3 * n * (n - 1) + 1;
}

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(103);
expect r0 == 3 * 103 * (103 - 1) + 1;
}

// REPEAT 4 - TIME: 7.7714935 s
