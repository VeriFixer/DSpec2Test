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

method {:test} Test30() {
var r0 := Min(109, 109);
expect r0 == 109 || r0 == 109;
expect r0 <= 109 && r0 <= 109;
}
method {:test} Test31() {
var r0 := Min(110, 109);
expect r0 == 110 || r0 == 109;
expect r0 <= 110 && r0 <= 109;
}

// REPEAT 7 - TIME: 16.3241242 s
