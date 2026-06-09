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

method {:test} Test32() {
var r0 := Min(111, 111);
expect r0 == 111 || r0 == 111;
expect r0 <= 111 && r0 <= 111;
}
method {:test} Test33() {
var r0 := Min(111, 110);
expect r0 == 111 || r0 == 110;
expect r0 <= 111 && r0 <= 110;
}

// REPEAT 8 - TIME: 15.5170225 s
