method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test8() {
expect -9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(9, -9);
expect r0 == 9 / -9;
}

// REPEAT 9 - TIME: 10.2565908 s
