method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(7);
expect r0 == 6 * 7 * (7 - 1) + 1;
}

// REPEAT 8 - TIME: 7.3138958 s
