method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test18() {
expect -91 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772316, -91);
expect r0 == 772316 / -91;
}

// REPEAT 10 - TIME: 13.3495727 s
