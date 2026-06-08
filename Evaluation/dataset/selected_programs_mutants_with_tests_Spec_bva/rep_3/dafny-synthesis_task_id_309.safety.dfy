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

method {:test} Test22() {
var r0 := Max(103, 103);
expect r0 == 103 || r0 == 103;
expect r0 >= 103 && r0 >= 103;
}
method {:test} Test23() {
var r0 := Max(103, 104);
expect r0 == 103 || r0 == 104;
expect r0 >= 103 && r0 >= 104;
}

// REPEAT 3 - TIME: 12.3417975 s
