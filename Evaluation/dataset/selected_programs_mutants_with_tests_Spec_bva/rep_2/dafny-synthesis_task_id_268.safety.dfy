method {:testEntry} StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    star := 6 * n * (n - 1) + 1;
}

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(101);
expect r0 == 6 * 101 * (101 - 1) + 1;
}

// REPEAT 2 - TIME: 5.2704288 s
