method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    decagonal := 4 * n * n - 3 * n;
}

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(9);
expect r0 == 4 * 9 * 9 - 3 * 9;
}

// REPEAT 10 - TIME: 10.26388 s
