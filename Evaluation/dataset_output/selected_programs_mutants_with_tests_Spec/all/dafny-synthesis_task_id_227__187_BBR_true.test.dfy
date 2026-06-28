// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if true {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}


method {:test} Test0() {
var r0 := MinOfThree(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0 || r0 == 0;
}
method {:test} Test1() {
var r0 := MinOfThree(1, 0, 0);
expect r0 <= 1 && r0 <= 0 && r0 <= 0;
expect r0 == 1 || r0 == 0 || r0 == 0;
}
method {:test} Test2() {
var r0 := MinOfThree(1, 1, 0);
expect r0 <= 1 && r0 <= 1 && r0 <= 0;
expect r0 == 1 || r0 == 1 || r0 == 0;
}

// REPEAT 1 - TIME: 3.3359905 s

method {:test} Test3() {
var r0 := MinOfThree(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
expect r0 == 2 || r0 == 2 || r0 == 2;
}
method {:test} Test4() {
var r0 := MinOfThree(3, 2, 2);
expect r0 <= 3 && r0 <= 2 && r0 <= 2;
expect r0 == 3 || r0 == 2 || r0 == 2;
}
method {:test} Test5() {
var r0 := MinOfThree(2, 2, 1);
expect r0 <= 2 && r0 <= 2 && r0 <= 1;
expect r0 == 2 || r0 == 2 || r0 == 1;
}

// REPEAT 2 - TIME: 5.401624 s

method {:test} Test6() {
var r0 := MinOfThree(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4 || r0 == 4;
}
method {:test} Test7() {
var r0 := MinOfThree(4, 3, 3);
expect r0 <= 4 && r0 <= 3 && r0 <= 3;
expect r0 == 4 || r0 == 3 || r0 == 3;
}
method {:test} Test8() {
var r0 := MinOfThree(4, 4, 3);
expect r0 <= 4 && r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 4 || r0 == 3;
}

// REPEAT 3 - TIME: 7.0020688 s

method {:test} Test9() {
var r0 := MinOfThree(5, 5, 5);
expect r0 <= 5 && r0 <= 5 && r0 <= 5;
expect r0 == 5 || r0 == 5 || r0 == 5;
}
method {:test} Test10() {
var r0 := MinOfThree(6, 5, 5);
expect r0 <= 6 && r0 <= 5 && r0 <= 5;
expect r0 == 6 || r0 == 5 || r0 == 5;
}
method {:test} Test11() {
var r0 := MinOfThree(6, 6, 5);
expect r0 <= 6 && r0 <= 6 && r0 <= 5;
expect r0 == 6 || r0 == 6 || r0 == 5;
}

// REPEAT 4 - TIME: 8.3408139 s

method {:test} Test12() {
var r0 := MinOfThree(7, 7, 7);
expect r0 <= 7 && r0 <= 7 && r0 <= 7;
expect r0 == 7 || r0 == 7 || r0 == 7;
}
method {:test} Test13() {
var r0 := MinOfThree(8, 7, 7);
expect r0 <= 8 && r0 <= 7 && r0 <= 7;
expect r0 == 8 || r0 == 7 || r0 == 7;
}
method {:test} Test14() {
var r0 := MinOfThree(7, 7, 6);
expect r0 <= 7 && r0 <= 7 && r0 <= 6;
expect r0 == 7 || r0 == 7 || r0 == 6;
}

// REPEAT 5 - TIME: 9.4392381 s

method {:test} Test15() {
var r0 := MinOfThree(9, 9, 9);
expect r0 <= 9 && r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9 || r0 == 9;
}
method {:test} Test16() {
var r0 := MinOfThree(9, 8, 8);
expect r0 <= 9 && r0 <= 8 && r0 <= 8;
expect r0 == 9 || r0 == 8 || r0 == 8;
}
method {:test} Test17() {
var r0 := MinOfThree(9, 9, 8);
expect r0 <= 9 && r0 <= 9 && r0 <= 8;
expect r0 == 9 || r0 == 9 || r0 == 8;
}

// REPEAT 6 - TIME: 10.611729 s

method {:test} Test18() {
var r0 := MinOfThree(10, 10, 10);
expect r0 <= 10 && r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10 || r0 == 10;
}
method {:test} Test19() {
var r0 := MinOfThree(11, 10, 10);
expect r0 <= 11 && r0 <= 10 && r0 <= 10;
expect r0 == 11 || r0 == 10 || r0 == 10;
}
method {:test} Test20() {
var r0 := MinOfThree(11, 11, 10);
expect r0 <= 11 && r0 <= 11 && r0 <= 10;
expect r0 == 11 || r0 == 11 || r0 == 10;
}

// REPEAT 7 - TIME: 12.095231 s

method {:test} Test21() {
var r0 := MinOfThree(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12 || r0 == 12;
}
method {:test} Test22() {
var r0 := MinOfThree(13, 12, 12);
expect r0 <= 13 && r0 <= 12 && r0 <= 12;
expect r0 == 13 || r0 == 12 || r0 == 12;
}
method {:test} Test23() {
var r0 := MinOfThree(12, 12, 11);
expect r0 <= 12 && r0 <= 12 && r0 <= 11;
expect r0 == 12 || r0 == 12 || r0 == 11;
}

// REPEAT 8 - TIME: 13.5181404 s

method {:test} Test24() {
var r0 := MinOfThree(14, 14, 14);
expect r0 <= 14 && r0 <= 14 && r0 <= 14;
expect r0 == 14 || r0 == 14 || r0 == 14;
}
method {:test} Test25() {
var r0 := MinOfThree(14, 13, 13);
expect r0 <= 14 && r0 <= 13 && r0 <= 13;
expect r0 == 14 || r0 == 13 || r0 == 13;
}
method {:test} Test26() {
var r0 := MinOfThree(14, 14, 13);
expect r0 <= 14 && r0 <= 14 && r0 <= 13;
expect r0 == 14 || r0 == 14 || r0 == 13;
}

// REPEAT 9 - TIME: 14.8951461 s

method {:test} Test27() {
var r0 := MinOfThree(15, 15, 15);
expect r0 <= 15 && r0 <= 15 && r0 <= 15;
expect r0 == 15 || r0 == 15 || r0 == 15;
}
method {:test} Test28() {
var r0 := MinOfThree(16, 15, 15);
expect r0 <= 16 && r0 <= 15 && r0 <= 15;
expect r0 == 16 || r0 == 15 || r0 == 15;
}
method {:test} Test29() {
var r0 := MinOfThree(16, 16, 15);
expect r0 <= 16 && r0 <= 16 && r0 <= 15;
expect r0 == 16 || r0 == 16 || r0 == 15;
}

// REPEAT 10 - TIME: 16.1499134 s
