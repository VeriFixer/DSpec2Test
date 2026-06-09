method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(3);
expect r0 == 6 * 3 * (3 - 1) + 1;
}

// REPEAT 4 - TIME: 4.3775444 s
