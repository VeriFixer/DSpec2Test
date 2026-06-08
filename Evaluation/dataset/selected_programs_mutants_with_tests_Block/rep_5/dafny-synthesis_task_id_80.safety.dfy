method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(4);
expect r0 == 4 * (4 + 1) * (4 + 2) / 6;
}

// REPEAT 5 - TIME: 5.4853625 s
