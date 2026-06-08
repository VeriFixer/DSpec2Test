method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(9);
expect r0 + 1 == 9;
}

// REPEAT 9 - TIME: 7.819761 s
