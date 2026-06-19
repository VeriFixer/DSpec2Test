// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  maxValue := a;
}


method {:test} Test0() {
var r0 := Max(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 >= 0 && r0 >= 0;
}
method {:test} Test1() {
var r0 := Max(-100, -100);
expect r0 == -100 || r0 == -100;
expect r0 >= -100 && r0 >= -100;
}
method {:test} Test2() {
var r0 := Max(100, 0);
expect r0 == 100 || r0 == 0;
expect r0 >= 100 && r0 >= 0;
}
method {:test} Test3() {
var r0 := Max(0, -100);
expect r0 == 0 || r0 == -100;
expect r0 >= 0 && r0 >= -100;
}
method {:test} Test4() {
var r0 := Max(100, 100);
expect r0 == 100 || r0 == 100;
expect r0 >= 100 && r0 >= 100;
}
method {:test} Test10() {
var r0 := Max(-1, 0);
expect r0 == -1 || r0 == 0;
expect r0 >= -1 && r0 >= 0;
}
method {:test} Test11() {
var r0 := Max(-100, 0);
expect r0 == -100 || r0 == 0;
expect r0 >= -100 && r0 >= 0;
}
method {:test} Test12() {
var r0 := Max(100, 101);
expect r0 == 100 || r0 == 101;
expect r0 >= 100 && r0 >= 101;
}
method {:test} Test13() {
var r0 := Max(-101, -100);
expect r0 == -101 || r0 == -100;
expect r0 >= -101 && r0 >= -100;
}
method {:test} Test14() {
var r0 := Max(0, 100);
expect r0 == 0 || r0 == 100;
expect r0 >= 0 && r0 >= 100;
}

// REPEAT 1 - TIME: 10.8377367 s

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

// REPEAT 2 - TIME: 11.97691 s

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

// REPEAT 3 - TIME: 12.9685546 s

method {:test} Test24() {
var r0 := Max(105, 105);
expect r0 == 105 || r0 == 105;
expect r0 >= 105 && r0 >= 105;
}
method {:test} Test25() {
var r0 := Max(104, 105);
expect r0 == 104 || r0 == 105;
expect r0 >= 104 && r0 >= 105;
}

// REPEAT 4 - TIME: 13.860255 s

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

// REPEAT 5 - TIME: 14.8590941 s

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

// REPEAT 6 - TIME: 15.9153935 s

method {:test} Test30() {
var r0 := Max(109, 109);
expect r0 == 109 || r0 == 109;
expect r0 >= 109 && r0 >= 109;
}
method {:test} Test31() {
var r0 := Max(109, 110);
expect r0 == 109 || r0 == 110;
expect r0 >= 109 && r0 >= 110;
}

// REPEAT 7 - TIME: 16.8998323 s

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

// REPEAT 8 - TIME: 17.865035 s

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

// REPEAT 9 - TIME: 18.8899309 s

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

// REPEAT 10 - TIME: 19.7534027 s
