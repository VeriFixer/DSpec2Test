method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    decagonal := 4 * n * n - 3 * n;
}

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(3);
expect r0 == 4 * 3 * 3 - 3 * 3;
}

// REPEAT 4 - TIME: 5.331968 s
