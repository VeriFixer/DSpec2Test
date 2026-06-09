method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(102);
expect r0 + 1 == 102;
}

// REPEAT 2 - TIME: 5.5141126 s
