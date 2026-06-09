method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(9);
expect r0 == 6 * 9 * (9 - 1) + 1;
}

// REPEAT 10 - TIME: 9.725106 s
