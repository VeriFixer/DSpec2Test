// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if !(x < y) {
    return x;
  } else {
    return y;
  }
}


method {:test} Test0() {
var r0 := Min(1, 0);
expect 1 <= 0 ==> r0 == 1;
expect 1 > 0 ==> r0 == 0;
}
method {:test} Test1() {
var r0 := Min(0, 0);
expect 0 <= 0 ==> r0 == 0;
expect 0 > 0 ==> r0 == 0;
}

// REPEAT 1 - TIME: 3.4963767 s

method {:test} Test2() {
var r0 := Min(2, 1);
expect 2 <= 1 ==> r0 == 2;
expect 2 > 1 ==> r0 == 1;
}
method {:test} Test3() {
var r0 := Min(2, 2);
expect 2 <= 2 ==> r0 == 2;
expect 2 > 2 ==> r0 == 2;
}

// REPEAT 2 - TIME: 5.0473034 s

method {:test} Test4() {
var r0 := Min(4, 3);
expect 4 <= 3 ==> r0 == 4;
expect 4 > 3 ==> r0 == 3;
}
method {:test} Test5() {
var r0 := Min(3, 3);
expect 3 <= 3 ==> r0 == 3;
expect 3 > 3 ==> r0 == 3;
}

// REPEAT 3 - TIME: 6.459395 s

method {:test} Test6() {
var r0 := Min(5, 4);
expect 5 <= 4 ==> r0 == 5;
expect 5 > 4 ==> r0 == 4;
}
method {:test} Test7() {
var r0 := Min(5, 5);
expect 5 <= 5 ==> r0 == 5;
expect 5 > 5 ==> r0 == 5;
}

// REPEAT 4 - TIME: 7.6292198 s

method {:test} Test8() {
var r0 := Min(7, 6);
expect 7 <= 6 ==> r0 == 7;
expect 7 > 6 ==> r0 == 6;
}
method {:test} Test9() {
var r0 := Min(6, 6);
expect 6 <= 6 ==> r0 == 6;
expect 6 > 6 ==> r0 == 6;
}

// REPEAT 5 - TIME: 8.7363048 s

method {:test} Test10() {
var r0 := Min(8, 7);
expect 8 <= 7 ==> r0 == 8;
expect 8 > 7 ==> r0 == 7;
}
method {:test} Test11() {
var r0 := Min(8, 8);
expect 8 <= 8 ==> r0 == 8;
expect 8 > 8 ==> r0 == 8;
}

// REPEAT 6 - TIME: 9.7170448 s

method {:test} Test12() {
var r0 := Min(10, 9);
expect 10 <= 9 ==> r0 == 10;
expect 10 > 9 ==> r0 == 9;
}
method {:test} Test13() {
var r0 := Min(9, 9);
expect 9 <= 9 ==> r0 == 9;
expect 9 > 9 ==> r0 == 9;
}

// REPEAT 7 - TIME: 10.4995693 s

method {:test} Test14() {
var r0 := Min(11, 10);
expect 11 <= 10 ==> r0 == 11;
expect 11 > 10 ==> r0 == 10;
}
method {:test} Test15() {
var r0 := Min(11, 11);
expect 11 <= 11 ==> r0 == 11;
expect 11 > 11 ==> r0 == 11;
}

// REPEAT 8 - TIME: 11.2760114 s

method {:test} Test16() {
var r0 := Min(13, 12);
expect 13 <= 12 ==> r0 == 13;
expect 13 > 12 ==> r0 == 12;
}
method {:test} Test17() {
var r0 := Min(12, 12);
expect 12 <= 12 ==> r0 == 12;
expect 12 > 12 ==> r0 == 12;
}

// REPEAT 9 - TIME: 12.0606807 s

method {:test} Test18() {
var r0 := Min(14, 13);
expect 14 <= 13 ==> r0 == 14;
expect 14 > 13 ==> r0 == 13;
}
method {:test} Test19() {
var r0 := Min(14, 14);
expect 14 <= 14 ==> r0 == 14;
expect 14 > 14 ==> r0 == 14;
}

// REPEAT 10 - TIME: 12.8265797 s
