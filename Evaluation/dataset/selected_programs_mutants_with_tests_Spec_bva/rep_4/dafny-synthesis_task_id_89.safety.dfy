method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
}

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(104);
expect r0 + 1 == 104;
}

// REPEAT 4 - TIME: 7.9313935 s
