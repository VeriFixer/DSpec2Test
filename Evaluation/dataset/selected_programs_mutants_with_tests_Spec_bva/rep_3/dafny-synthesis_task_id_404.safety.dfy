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

method {:test} Test22() {
var r0 := Min(103, 103);
expect r0 == 103 || r0 == 103;
expect r0 <= 103 && r0 <= 103;
}
method {:test} Test23() {
var r0 := Min(104, 103);
expect r0 == 104 || r0 == 103;
expect r0 <= 104 && r0 <= 103;
}

// REPEAT 3 - TIME: 11.5654752 s
