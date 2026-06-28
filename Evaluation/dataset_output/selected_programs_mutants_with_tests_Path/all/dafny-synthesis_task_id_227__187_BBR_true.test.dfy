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
var r0 := MinOfThree(0, 0, -1);
expect r0 <= 0 && r0 <= 0 && r0 <= -1;
expect r0 == 0 || r0 == 0 || r0 == -1;
}
method {:test} Test2() {
var r0 := MinOfThree(0, 1, -1);
expect r0 <= 0 && r0 <= 1 && r0 <= -1;
expect r0 == 0 || r0 == 1 || r0 == -1;
}
method {:test} Test3() {
var r0 := MinOfThree(1, 0, 0);
expect r0 <= 1 && r0 <= 0 && r0 <= 0;
expect r0 == 1 || r0 == 0 || r0 == 0;
}
method {:test} Test4() {
var r0 := MinOfThree(1, 0, -1);
expect r0 <= 1 && r0 <= 0 && r0 <= -1;
expect r0 == 1 || r0 == 0 || r0 == -1;
}

// REPEAT 1 - TIME: 6.8712224 s

method {:test} Test5() {
var r0 := MinOfThree(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
expect r0 == 2 || r0 == 2 || r0 == 2;
}
method {:test} Test6() {
var r0 := MinOfThree(2, 2, 1);
expect r0 <= 2 && r0 <= 2 && r0 <= 1;
expect r0 == 2 || r0 == 2 || r0 == 1;
}
method {:test} Test7() {
var r0 := MinOfThree(2, 3, 1);
expect r0 <= 2 && r0 <= 3 && r0 <= 1;
expect r0 == 2 || r0 == 3 || r0 == 1;
}
method {:test} Test8() {
var r0 := MinOfThree(3, 2, 2);
expect r0 <= 3 && r0 <= 2 && r0 <= 2;
expect r0 == 3 || r0 == 2 || r0 == 2;
}
method {:test} Test9() {
var r0 := MinOfThree(3, 2, 1);
expect r0 <= 3 && r0 <= 2 && r0 <= 1;
expect r0 == 3 || r0 == 2 || r0 == 1;
}

// REPEAT 2 - TIME: 10.8346269 s

method {:test} Test10() {
var r0 := MinOfThree(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4 || r0 == 4;
}
method {:test} Test11() {
var r0 := MinOfThree(4, 4, 3);
expect r0 <= 4 && r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 4 || r0 == 3;
}
method {:test} Test12() {
var r0 := MinOfThree(4, 5, 3);
expect r0 <= 4 && r0 <= 5 && r0 <= 3;
expect r0 == 4 || r0 == 5 || r0 == 3;
}
method {:test} Test13() {
var r0 := MinOfThree(5, 4, 4);
expect r0 <= 5 && r0 <= 4 && r0 <= 4;
expect r0 == 5 || r0 == 4 || r0 == 4;
}
method {:test} Test14() {
var r0 := MinOfThree(5, 4, 3);
expect r0 <= 5 && r0 <= 4 && r0 <= 3;
expect r0 == 5 || r0 == 4 || r0 == 3;
}

// REPEAT 3 - TIME: 14.6325257 s

method {:test} Test15() {
var r0 := MinOfThree(6, 6, 6);
expect r0 <= 6 && r0 <= 6 && r0 <= 6;
expect r0 == 6 || r0 == 6 || r0 == 6;
}
method {:test} Test16() {
var r0 := MinOfThree(6, 6, 5);
expect r0 <= 6 && r0 <= 6 && r0 <= 5;
expect r0 == 6 || r0 == 6 || r0 == 5;
}
method {:test} Test17() {
var r0 := MinOfThree(6, 7, 5);
expect r0 <= 6 && r0 <= 7 && r0 <= 5;
expect r0 == 6 || r0 == 7 || r0 == 5;
}
method {:test} Test18() {
var r0 := MinOfThree(7, 6, 6);
expect r0 <= 7 && r0 <= 6 && r0 <= 6;
expect r0 == 7 || r0 == 6 || r0 == 6;
}
method {:test} Test19() {
var r0 := MinOfThree(7, 6, 5);
expect r0 <= 7 && r0 <= 6 && r0 <= 5;
expect r0 == 7 || r0 == 6 || r0 == 5;
}

// REPEAT 4 - TIME: 18.9220085 s

method {:test} Test20() {
var r0 := MinOfThree(8, 8, 8);
expect r0 <= 8 && r0 <= 8 && r0 <= 8;
expect r0 == 8 || r0 == 8 || r0 == 8;
}
method {:test} Test21() {
var r0 := MinOfThree(8, 8, 7);
expect r0 <= 8 && r0 <= 8 && r0 <= 7;
expect r0 == 8 || r0 == 8 || r0 == 7;
}
method {:test} Test22() {
var r0 := MinOfThree(8, 9, 7);
expect r0 <= 8 && r0 <= 9 && r0 <= 7;
expect r0 == 8 || r0 == 9 || r0 == 7;
}
method {:test} Test23() {
var r0 := MinOfThree(9, 8, 8);
expect r0 <= 9 && r0 <= 8 && r0 <= 8;
expect r0 == 9 || r0 == 8 || r0 == 8;
}
method {:test} Test24() {
var r0 := MinOfThree(9, 8, 7);
expect r0 <= 9 && r0 <= 8 && r0 <= 7;
expect r0 == 9 || r0 == 8 || r0 == 7;
}

// REPEAT 5 - TIME: 23.9212048 s

method {:test} Test25() {
var r0 := MinOfThree(10, 10, 10);
expect r0 <= 10 && r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10 || r0 == 10;
}
method {:test} Test26() {
var r0 := MinOfThree(10, 10, 9);
expect r0 <= 10 && r0 <= 10 && r0 <= 9;
expect r0 == 10 || r0 == 10 || r0 == 9;
}
method {:test} Test27() {
var r0 := MinOfThree(10, 11, 9);
expect r0 <= 10 && r0 <= 11 && r0 <= 9;
expect r0 == 10 || r0 == 11 || r0 == 9;
}
method {:test} Test28() {
var r0 := MinOfThree(11, 10, 10);
expect r0 <= 11 && r0 <= 10 && r0 <= 10;
expect r0 == 11 || r0 == 10 || r0 == 10;
}
method {:test} Test29() {
var r0 := MinOfThree(11, 10, 9);
expect r0 <= 11 && r0 <= 10 && r0 <= 9;
expect r0 == 11 || r0 == 10 || r0 == 9;
}

// REPEAT 6 - TIME: 29.4499403 s

method {:test} Test30() {
var r0 := MinOfThree(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12 || r0 == 12;
}
method {:test} Test31() {
var r0 := MinOfThree(12, 12, 11);
expect r0 <= 12 && r0 <= 12 && r0 <= 11;
expect r0 == 12 || r0 == 12 || r0 == 11;
}
method {:test} Test32() {
var r0 := MinOfThree(12, 13, 11);
expect r0 <= 12 && r0 <= 13 && r0 <= 11;
expect r0 == 12 || r0 == 13 || r0 == 11;
}
method {:test} Test33() {
var r0 := MinOfThree(13, 12, 12);
expect r0 <= 13 && r0 <= 12 && r0 <= 12;
expect r0 == 13 || r0 == 12 || r0 == 12;
}
method {:test} Test34() {
var r0 := MinOfThree(13, 12, 11);
expect r0 <= 13 && r0 <= 12 && r0 <= 11;
expect r0 == 13 || r0 == 12 || r0 == 11;
}

// REPEAT 7 - TIME: 34.4800656 s

method {:test} Test35() {
var r0 := MinOfThree(14, 14, 14);
expect r0 <= 14 && r0 <= 14 && r0 <= 14;
expect r0 == 14 || r0 == 14 || r0 == 14;
}
method {:test} Test36() {
var r0 := MinOfThree(14, 14, 13);
expect r0 <= 14 && r0 <= 14 && r0 <= 13;
expect r0 == 14 || r0 == 14 || r0 == 13;
}
method {:test} Test37() {
var r0 := MinOfThree(14, 15, 13);
expect r0 <= 14 && r0 <= 15 && r0 <= 13;
expect r0 == 14 || r0 == 15 || r0 == 13;
}
method {:test} Test38() {
var r0 := MinOfThree(15, 14, 14);
expect r0 <= 15 && r0 <= 14 && r0 <= 14;
expect r0 == 15 || r0 == 14 || r0 == 14;
}
method {:test} Test39() {
var r0 := MinOfThree(15, 14, 13);
expect r0 <= 15 && r0 <= 14 && r0 <= 13;
expect r0 == 15 || r0 == 14 || r0 == 13;
}

// REPEAT 8 - TIME: 39.9184284 s

method {:test} Test40() {
var r0 := MinOfThree(16, 16, 16);
expect r0 <= 16 && r0 <= 16 && r0 <= 16;
expect r0 == 16 || r0 == 16 || r0 == 16;
}
method {:test} Test41() {
var r0 := MinOfThree(16, 16, 15);
expect r0 <= 16 && r0 <= 16 && r0 <= 15;
expect r0 == 16 || r0 == 16 || r0 == 15;
}
method {:test} Test42() {
var r0 := MinOfThree(16, 17, 15);
expect r0 <= 16 && r0 <= 17 && r0 <= 15;
expect r0 == 16 || r0 == 17 || r0 == 15;
}
method {:test} Test43() {
var r0 := MinOfThree(17, 16, 16);
expect r0 <= 17 && r0 <= 16 && r0 <= 16;
expect r0 == 17 || r0 == 16 || r0 == 16;
}
method {:test} Test44() {
var r0 := MinOfThree(17, 16, 15);
expect r0 <= 17 && r0 <= 16 && r0 <= 15;
expect r0 == 17 || r0 == 16 || r0 == 15;
}

// REPEAT 9 - TIME: 45.1474813 s

method {:test} Test45() {
var r0 := MinOfThree(18, 18, 18);
expect r0 <= 18 && r0 <= 18 && r0 <= 18;
expect r0 == 18 || r0 == 18 || r0 == 18;
}
method {:test} Test46() {
var r0 := MinOfThree(18, 18, 17);
expect r0 <= 18 && r0 <= 18 && r0 <= 17;
expect r0 == 18 || r0 == 18 || r0 == 17;
}
method {:test} Test47() {
var r0 := MinOfThree(18, 19, 17);
expect r0 <= 18 && r0 <= 19 && r0 <= 17;
expect r0 == 18 || r0 == 19 || r0 == 17;
}
method {:test} Test48() {
var r0 := MinOfThree(19, 18, 18);
expect r0 <= 19 && r0 <= 18 && r0 <= 18;
expect r0 == 19 || r0 == 18 || r0 == 18;
}
method {:test} Test49() {
var r0 := MinOfThree(19, 18, 17);
expect r0 <= 19 && r0 <= 18 && r0 <= 17;
expect r0 == 19 || r0 == 18 || r0 == 17;
}

// REPEAT 10 - TIME: 51.5181455 s
