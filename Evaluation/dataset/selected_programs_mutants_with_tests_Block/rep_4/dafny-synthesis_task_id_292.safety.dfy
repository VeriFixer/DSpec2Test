method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test3() {
expect -4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8360, -4);
expect r0 == -8360 / -4;
}

// REPEAT 4 - TIME: 4.1937772 s
