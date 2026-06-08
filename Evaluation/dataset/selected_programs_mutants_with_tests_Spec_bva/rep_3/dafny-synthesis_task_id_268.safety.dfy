method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(102);
expect r0 == 6 * 102 * (102 - 1) + 1;
}

// REPEAT 3 - TIME: 6.7705265 s
