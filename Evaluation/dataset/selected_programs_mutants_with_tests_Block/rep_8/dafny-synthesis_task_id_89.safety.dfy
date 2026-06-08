method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(8);
expect r0 + 1 == 8;
}

// REPEAT 8 - TIME: 7.248162 s
