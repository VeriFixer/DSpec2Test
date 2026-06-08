method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test15() {
expect 110 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(110);
expect r0 + 1 == 110;
}

// REPEAT 10 - TIME: 12.1022471 s
