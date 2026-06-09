method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(4);
expect r0 + 1 == 4;
}

// REPEAT 4 - TIME: 4.9062424 s
