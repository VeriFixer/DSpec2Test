method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(8);
expect r0 == 6 * 8 * (8 - 1) + 1;
}

// REPEAT 9 - TIME: 10.1184397 s
