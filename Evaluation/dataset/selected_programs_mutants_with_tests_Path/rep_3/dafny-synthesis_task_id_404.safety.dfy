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

method {:test} Test4() {
var r0 := Min(3, 3);
expect r0 == 3 || r0 == 3;
expect r0 <= 3 && r0 <= 3;
}
method {:test} Test5() {
var r0 := Min(4, 3);
expect r0 == 4 || r0 == 3;
expect r0 <= 4 && r0 <= 3;
}

// REPEAT 3 - TIME: 3.0594048 s
