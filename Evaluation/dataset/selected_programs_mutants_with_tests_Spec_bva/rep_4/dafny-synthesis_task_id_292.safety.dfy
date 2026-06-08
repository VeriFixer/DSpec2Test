method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test12() {
expect -97 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772022, -97);
expect r0 == 772022 / -97;
}

// REPEAT 4 - TIME: 8.9554751 s
