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

method {:test} Test34() {
var r0 := Max(112, 112);
expect r0 == 112 || r0 == 112;
expect r0 >= 112 && r0 >= 112;
}
method {:test} Test35() {
var r0 := Max(112, 113);
expect r0 == 112 || r0 == 113;
expect r0 >= 112 && r0 >= 113;
}

// REPEAT 9 - TIME: 18.018737 s
