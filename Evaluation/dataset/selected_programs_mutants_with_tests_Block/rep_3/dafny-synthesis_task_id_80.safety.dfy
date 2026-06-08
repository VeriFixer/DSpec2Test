method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(2);
expect r0 == 2 * (2 + 1) * (2 + 2) / 6;
}

// REPEAT 3 - TIME: 3.8768587 s
