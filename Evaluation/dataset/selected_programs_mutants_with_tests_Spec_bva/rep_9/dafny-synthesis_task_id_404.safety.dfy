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

method {:test} Test34() {
var r0 := Min(112, 112);
expect r0 == 112 || r0 == 112;
expect r0 <= 112 && r0 <= 112;
}
method {:test} Test35() {
var r0 := Min(113, 112);
expect r0 == 113 || r0 == 112;
expect r0 <= 113 && r0 <= 112;
}

// REPEAT 9 - TIME: 18.0912845 s
