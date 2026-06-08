method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(106);
expect r0 == 6 * 106 * (106 - 1) + 1;
}

// REPEAT 7 - TIME: 10.177761 s
