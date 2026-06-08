method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    decagonal := 4 * n * n - 3 * n;
}

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(8);
expect r0 == 4 * 8 * 8 - 3 * 8;
}

// REPEAT 9 - TIME: 7.9073787 s
