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

method {:test} Test26() {
var r0 := Min(106, 106);
expect r0 == 106 || r0 == 106;
expect r0 <= 106 && r0 <= 106;
}
method {:test} Test27() {
var r0 := Min(107, 106);
expect r0 == 107 || r0 == 106;
expect r0 <= 107 && r0 <= 106;
}

// REPEAT 5 - TIME: 13.2047207 s
