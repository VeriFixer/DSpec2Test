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

method {:test} Test20() {
var r0 := Min(102, 102);
expect r0 == 102 || r0 == 102;
expect r0 <= 102 && r0 <= 102;
}
method {:test} Test21() {
var r0 := Min(102, 101);
expect r0 == 102 || r0 == 101;
expect r0 <= 102 && r0 <= 101;
}

// REPEAT 2 - TIME: 11.7700506 s
