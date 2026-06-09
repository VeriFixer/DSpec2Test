method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(4);
expect r0 == 6 * 4 * (4 - 1) + 1;
}

// REPEAT 5 - TIME: 6.1009945 s
