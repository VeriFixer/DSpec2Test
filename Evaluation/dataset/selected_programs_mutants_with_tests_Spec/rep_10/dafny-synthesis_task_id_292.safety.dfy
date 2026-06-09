method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test9() {
expect -10 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(10, -10);
expect r0 == 10 / -10;
}

// REPEAT 10 - TIME: 9.2173278 s
