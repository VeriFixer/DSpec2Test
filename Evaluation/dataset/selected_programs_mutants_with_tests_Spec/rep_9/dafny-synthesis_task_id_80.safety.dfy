method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(8);
expect r0 == 8 * (8 + 1) * (8 + 2) / 6;
}

// REPEAT 9 - TIME: 9.5532003 s
