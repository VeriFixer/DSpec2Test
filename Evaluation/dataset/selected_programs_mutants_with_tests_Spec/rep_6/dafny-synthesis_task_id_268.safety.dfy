method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(5);
expect r0 == 6 * 5 * (5 - 1) + 1;
}

// REPEAT 6 - TIME: 6.9068553 s
