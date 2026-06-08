method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test16() {
expect -93 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772178, -93);
expect r0 == 772178 / -93;
}

// REPEAT 8 - TIME: 11.8221285 s
