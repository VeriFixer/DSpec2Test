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

method {:test} Test28() {
var r0 := Max(108, 108);
expect r0 == 108 || r0 == 108;
expect r0 >= 108 && r0 >= 108;
}
method {:test} Test29() {
var r0 := Max(107, 108);
expect r0 == 107 || r0 == 108;
expect r0 >= 107 && r0 >= 108;
}

// REPEAT 6 - TIME: 13.7395562 s
