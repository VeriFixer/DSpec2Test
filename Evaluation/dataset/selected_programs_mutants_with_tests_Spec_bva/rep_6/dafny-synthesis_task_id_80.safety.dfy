method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(105);
expect r0 == 105 * (105 + 1) * (105 + 2) / 6;
}

// REPEAT 6 - TIME: 9.1064564 s
