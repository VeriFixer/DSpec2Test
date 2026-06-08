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

method {:test} Test26() {
var r0 := Max(106, 106);
expect r0 == 106 || r0 == 106;
expect r0 >= 106 && r0 >= 106;
}
method {:test} Test27() {
var r0 := Max(106, 107);
expect r0 == 106 || r0 == 107;
expect r0 >= 106 && r0 >= 107;
}

// REPEAT 5 - TIME: 14.5027754 s
