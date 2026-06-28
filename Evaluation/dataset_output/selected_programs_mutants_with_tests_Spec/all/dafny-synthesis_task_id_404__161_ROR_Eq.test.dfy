// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a == b {
    minValue := a;
  } else {
    minValue := b;
  }
}


method {:test} Test0() {
var r0 := Min(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
var r0 := Min(1, 0);
expect r0 == 1 || r0 == 0;
expect r0 <= 1 && r0 <= 0;
}

// REPEAT 1 - TIME: 3.3362997 s

method {:test} Test2() {
var r0 := Min(2, 2);
expect r0 == 2 || r0 == 2;
expect r0 <= 2 && r0 <= 2;
}
method {:test} Test3() {
var r0 := Min(2, 1);
expect r0 == 2 || r0 == 1;
expect r0 <= 2 && r0 <= 1;
}

// REPEAT 2 - TIME: 4.8162214 s

method {:test} Test4() {
var r0 := Min(3, 3);
expect r0 == 3 || r0 == 3;
expect r0 <= 3 && r0 <= 3;
}
method {:test} Test5() {
var r0 := Min(4, 3);
expect r0 == 4 || r0 == 3;
expect r0 <= 4 && r0 <= 3;
}

// REPEAT 3 - TIME: 6.2287314 s

method {:test} Test6() {
var r0 := Min(5, 5);
expect r0 == 5 || r0 == 5;
expect r0 <= 5 && r0 <= 5;
}
method {:test} Test7() {
var r0 := Min(5, 4);
expect r0 == 5 || r0 == 4;
expect r0 <= 5 && r0 <= 4;
}

// REPEAT 4 - TIME: 7.6298677 s

method {:test} Test8() {
var r0 := Min(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 <= 6 && r0 <= 6;
}
method {:test} Test9() {
var r0 := Min(7, 6);
expect r0 == 7 || r0 == 6;
expect r0 <= 7 && r0 <= 6;
}

// REPEAT 5 - TIME: 8.8877971 s

method {:test} Test10() {
var r0 := Min(8, 8);
expect r0 == 8 || r0 == 8;
expect r0 <= 8 && r0 <= 8;
}
method {:test} Test11() {
var r0 := Min(8, 7);
expect r0 == 8 || r0 == 7;
expect r0 <= 8 && r0 <= 7;
}

// REPEAT 6 - TIME: 10.0095906 s

method {:test} Test12() {
var r0 := Min(9, 9);
expect r0 == 9 || r0 == 9;
expect r0 <= 9 && r0 <= 9;
}
method {:test} Test13() {
var r0 := Min(10, 9);
expect r0 == 10 || r0 == 9;
expect r0 <= 10 && r0 <= 9;
}

// REPEAT 7 - TIME: 11.2282016 s

method {:test} Test14() {
var r0 := Min(11, 11);
expect r0 == 11 || r0 == 11;
expect r0 <= 11 && r0 <= 11;
}
method {:test} Test15() {
var r0 := Min(11, 10);
expect r0 == 11 || r0 == 10;
expect r0 <= 11 && r0 <= 10;
}

// REPEAT 8 - TIME: 12.5148686 s

method {:test} Test16() {
var r0 := Min(12, 12);
expect r0 == 12 || r0 == 12;
expect r0 <= 12 && r0 <= 12;
}
method {:test} Test17() {
var r0 := Min(13, 12);
expect r0 == 13 || r0 == 12;
expect r0 <= 13 && r0 <= 12;
}

// REPEAT 9 - TIME: 13.5174771 s

method {:test} Test18() {
var r0 := Min(14, 14);
expect r0 == 14 || r0 == 14;
expect r0 <= 14 && r0 <= 14;
}
method {:test} Test19() {
var r0 := Min(14, 13);
expect r0 == 14 || r0 == 13;
expect r0 <= 14 && r0 <= 13;
}

// REPEAT 10 - TIME: 14.6258298 s
