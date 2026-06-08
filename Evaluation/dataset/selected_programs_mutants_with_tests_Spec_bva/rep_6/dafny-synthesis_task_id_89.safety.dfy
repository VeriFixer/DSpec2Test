method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(106);
expect r0 + 1 == 106;
}

// REPEAT 6 - TIME: 9.550492 s
