method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test1() {
expect -2 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8364, -2);
expect r0 == -8364 / -2;
}

// REPEAT 2 - TIME: 3.2423698 s
