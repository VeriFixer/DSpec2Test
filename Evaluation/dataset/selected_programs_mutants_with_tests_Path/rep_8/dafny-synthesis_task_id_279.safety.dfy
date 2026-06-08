method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    decagonal := 4 * n * n - 3 * n;
}

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(7);
expect r0 == 4 * 7 * 7 - 3 * 7;
}

// REPEAT 8 - TIME: 9.9303492 s
