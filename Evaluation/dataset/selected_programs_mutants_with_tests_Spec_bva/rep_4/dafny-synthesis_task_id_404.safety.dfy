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

method {:test} Test24() {
var r0 := Min(105, 105);
expect r0 == 105 || r0 == 105;
expect r0 <= 105 && r0 <= 105;
}
method {:test} Test25() {
var r0 := Min(105, 104);
expect r0 == 105 || r0 == 104;
expect r0 <= 105 && r0 <= 104;
}

// REPEAT 4 - TIME: 13.6579135 s
