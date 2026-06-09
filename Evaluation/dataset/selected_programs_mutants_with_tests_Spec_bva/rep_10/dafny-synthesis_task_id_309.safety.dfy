method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
{
    if a >= b {
        maxValue := a;
    } else {
        maxValue := b;
    }
}

method {:test} Test36() {
var r0 := Max(114, 114);
expect r0 == 114 || r0 == 114;
expect r0 >= 114 && r0 >= 114;
}
method {:test} Test37() {
var r0 := Max(113, 114);
expect r0 == 113 || r0 == 114;
expect r0 >= 113 && r0 >= 114;
}

// REPEAT 10 - TIME: 17.0351091 s
