method {:testEntry} Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    result := a / b;
}

method {:test} Test10() {
expect -99 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(771902, -99);
expect r0 == 771902 / -99;
}

// REPEAT 2 - TIME: 7.4548347 s
