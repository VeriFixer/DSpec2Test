method {:testEntry} Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
{
    if a <= b {
        minValue := a;
    } else {
        minValue := b;
    }
}

method {:test} Test28() {
var r0 := Min(108, 108);
expect r0 == 108 || r0 == 108;
expect r0 <= 108 && r0 <= 108;
}
method {:test} Test29() {
var r0 := Min(108, 107);
expect r0 == 108 || r0 == 107;
expect r0 <= 108 && r0 <= 107;
}

// REPEAT 6 - TIME: 13.9701556 s
