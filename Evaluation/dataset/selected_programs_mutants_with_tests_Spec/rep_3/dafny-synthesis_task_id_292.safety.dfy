method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test2() {
expect -3 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8361, -3);
expect r0 == -8361 / -3;
}

// REPEAT 3 - TIME: 5.1577094 s
