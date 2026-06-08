method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    result := 3 * n * (n - 1) + 1;
}

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(102);
expect r0 == 3 * 102 * (102 - 1) + 1;
}

// REPEAT 3 - TIME: 7.0566439 s
