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

method {:test} Test20() {
var r0 := Max(102, 102);
expect r0 == 102 || r0 == 102;
expect r0 >= 102 && r0 >= 102;
}
method {:test} Test21() {
var r0 := Max(101, 102);
expect r0 == 101 || r0 == 102;
expect r0 >= 101 && r0 >= 102;
}

// REPEAT 2 - TIME: 10.2455328 s
