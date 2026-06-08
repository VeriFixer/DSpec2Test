method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    result := 3 * n * (n - 1) + 1;
}

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(8);
expect r0 == 3 * 8 * (8 - 1) + 1;
}

// REPEAT 8 - TIME: 8.506335 s
