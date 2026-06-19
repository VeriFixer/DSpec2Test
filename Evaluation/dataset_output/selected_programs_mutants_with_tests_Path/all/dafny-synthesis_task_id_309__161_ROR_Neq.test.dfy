// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  if a != b {
    maxValue := a;
  } else {
    maxValue := b;
  }
}


method {:test} Test0() {
var r0 := Max(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 >= 0 && r0 >= 0;
}
method {:test} Test1() {
var r0 := Max(-1, 0);
expect r0 == -1 || r0 == 0;
expect r0 >= -1 && r0 >= 0;
}

// REPEAT 1 - TIME: 4.0626413 s

method {:test} Test2() {
var r0 := Max(1, 1);
expect r0 == 1 || r0 == 1;
expect r0 >= 1 && r0 >= 1;
}
method {:test} Test3() {
var r0 := Max(1, 2);
expect r0 == 1 || r0 == 2;
expect r0 >= 1 && r0 >= 2;
}

// REPEAT 2 - TIME: 5.8127717 s

method {:test} Test4() {
var r0 := Max(3, 3);
expect r0 == 3 || r0 == 3;
expect r0 >= 3 && r0 >= 3;
}
method {:test} Test5() {
var r0 := Max(2, 3);
expect r0 == 2 || r0 == 3;
expect r0 >= 2 && r0 >= 3;
}

// REPEAT 3 - TIME: 7.697484 s

method {:test} Test6() {
var r0 := Max(4, 4);
expect r0 == 4 || r0 == 4;
expect r0 >= 4 && r0 >= 4;
}
method {:test} Test7() {
var r0 := Max(4, 5);
expect r0 == 4 || r0 == 5;
expect r0 >= 4 && r0 >= 5;
}

// REPEAT 4 - TIME: 9.4467675 s

method {:test} Test8() {
var r0 := Max(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 >= 6 && r0 >= 6;
}
method {:test} Test9() {
var r0 := Max(5, 6);
expect r0 == 5 || r0 == 6;
expect r0 >= 5 && r0 >= 6;
}

// REPEAT 5 - TIME: 11.1644969 s

method {:test} Test10() {
var r0 := Max(7, 7);
expect r0 == 7 || r0 == 7;
expect r0 >= 7 && r0 >= 7;
}
method {:test} Test11() {
var r0 := Max(7, 8);
expect r0 == 7 || r0 == 8;
expect r0 >= 7 && r0 >= 8;
}

// REPEAT 6 - TIME: 12.250023 s

method {:test} Test12() {
var r0 := Max(9, 9);
expect r0 == 9 || r0 == 9;
expect r0 >= 9 && r0 >= 9;
}
method {:test} Test13() {
var r0 := Max(8, 9);
expect r0 == 8 || r0 == 9;
expect r0 >= 8 && r0 >= 9;
}

// REPEAT 7 - TIME: 13.3797122 s

method {:test} Test14() {
var r0 := Max(10, 10);
expect r0 == 10 || r0 == 10;
expect r0 >= 10 && r0 >= 10;
}
method {:test} Test15() {
var r0 := Max(10, 11);
expect r0 == 10 || r0 == 11;
expect r0 >= 10 && r0 >= 11;
}

// REPEAT 8 - TIME: 14.761721 s

method {:test} Test16() {
var r0 := Max(12, 12);
expect r0 == 12 || r0 == 12;
expect r0 >= 12 && r0 >= 12;
}
method {:test} Test17() {
var r0 := Max(11, 12);
expect r0 == 11 || r0 == 12;
expect r0 >= 11 && r0 >= 12;
}

// REPEAT 9 - TIME: 16.1578397 s

method {:test} Test18() {
var r0 := Max(13, 13);
expect r0 == 13 || r0 == 13;
expect r0 >= 13 && r0 >= 13;
}
method {:test} Test19() {
var r0 := Max(13, 14);
expect r0 == 13 || r0 == 14;
expect r0 >= 13 && r0 >= 14;
}

// REPEAT 10 - TIME: 17.5076097 s
