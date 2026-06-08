method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(6);
expect r0 == 6 * (6 + 1) * (6 + 2) / 6;
}

// REPEAT 7 - TIME: 8.2515539 s
