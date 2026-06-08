method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    result := 3 * n * (n - 1) + 1;
}

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(107);
expect r0 == 3 * 107 * (107 - 1) + 1;
}

// REPEAT 8 - TIME: 10.3942119 s
