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

method {:test} Test32() {
var r0 := Max(111, 111);
expect r0 == 111 || r0 == 111;
expect r0 >= 111 && r0 >= 111;
}
method {:test} Test33() {
var r0 := Max(110, 111);
expect r0 == 110 || r0 == 111;
expect r0 >= 110 && r0 >= 111;
}

// REPEAT 8 - TIME: 16.9918456 s
