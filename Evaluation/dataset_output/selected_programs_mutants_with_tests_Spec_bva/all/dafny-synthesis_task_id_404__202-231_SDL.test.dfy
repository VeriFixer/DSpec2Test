// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a <= b {
    minValue := a;
  }
}


method {:test} Test0() {
var r0 := Min(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
var r0 := Min(-100, 0);
expect r0 == -100 || r0 == 0;
expect r0 <= -100 && r0 <= 0;
}
method {:test} Test2() {
var r0 := Min(100, 100);
expect r0 == 100 || r0 == 100;
expect r0 <= 100 && r0 <= 100;
}
method {:test} Test3() {
var r0 := Min(-100, -100);
expect r0 == -100 || r0 == -100;
expect r0 <= -100 && r0 <= -100;
}
method {:test} Test4() {
var r0 := Min(0, 100);
expect r0 == 0 || r0 == 100;
expect r0 <= 0 && r0 <= 100;
}
method {:test} Test10() {
var r0 := Min(1, 0);
expect r0 == 1 || r0 == 0;
expect r0 <= 1 && r0 <= 0;
}
method {:test} Test11() {
var r0 := Min(-100, -101);
expect r0 == -100 || r0 == -101;
expect r0 <= -100 && r0 <= -101;
}
method {:test} Test12() {
var r0 := Min(100, 0);
expect r0 == 100 || r0 == 0;
expect r0 <= 100 && r0 <= 0;
}
method {:test} Test13() {
var r0 := Min(0, -100);
expect r0 == 0 || r0 == -100;
expect r0 <= 0 && r0 <= -100;
}
method {:test} Test14() {
var r0 := Min(101, 100);
expect r0 == 101 || r0 == 100;
expect r0 <= 101 && r0 <= 100;
}

// REPEAT 1 - TIME: 10.5278767 s

method {:test} Test20() {
var r0 := Min(102, 102);
expect r0 == 102 || r0 == 102;
expect r0 <= 102 && r0 <= 102;
}
method {:test} Test21() {
var r0 := Min(102, 101);
expect r0 == 102 || r0 == 101;
expect r0 <= 102 && r0 <= 101;
}

// REPEAT 2 - TIME: 11.5897343 s

method {:test} Test22() {
var r0 := Min(103, 103);
expect r0 == 103 || r0 == 103;
expect r0 <= 103 && r0 <= 103;
}
method {:test} Test23() {
var r0 := Min(104, 103);
expect r0 == 104 || r0 == 103;
expect r0 <= 104 && r0 <= 103;
}

// REPEAT 3 - TIME: 12.58067 s

method {:test} Test24() {
var r0 := Min(105, 105);
expect r0 == 105 || r0 == 105;
expect r0 <= 105 && r0 <= 105;
}
method {:test} Test25() {
var r0 := Min(105, 104);
expect r0 == 105 || r0 == 104;
expect r0 <= 105 && r0 <= 104;
}

// REPEAT 4 - TIME: 13.5909765 s

method {:test} Test26() {
var r0 := Min(106, 106);
expect r0 == 106 || r0 == 106;
expect r0 <= 106 && r0 <= 106;
}
method {:test} Test27() {
var r0 := Min(107, 106);
expect r0 == 107 || r0 == 106;
expect r0 <= 107 && r0 <= 106;
}

// REPEAT 5 - TIME: 14.5119375 s

method {:test} Test28() {
var r0 := Min(108, 108);
expect r0 == 108 || r0 == 108;
expect r0 <= 108 && r0 <= 108;
}
method {:test} Test29() {
var r0 := Min(108, 107);
expect r0 == 108 || r0 == 107;
expect r0 <= 108 && r0 <= 107;
}

// REPEAT 6 - TIME: 15.3651815 s

method {:test} Test30() {
var r0 := Min(109, 109);
expect r0 == 109 || r0 == 109;
expect r0 <= 109 && r0 <= 109;
}
method {:test} Test31() {
var r0 := Min(110, 109);
expect r0 == 110 || r0 == 109;
expect r0 <= 110 && r0 <= 109;
}

// REPEAT 7 - TIME: 16.249803 s

method {:test} Test32() {
var r0 := Min(111, 111);
expect r0 == 111 || r0 == 111;
expect r0 <= 111 && r0 <= 111;
}
method {:test} Test33() {
var r0 := Min(111, 110);
expect r0 == 111 || r0 == 110;
expect r0 <= 111 && r0 <= 110;
}

// REPEAT 8 - TIME: 17.139022 s

method {:test} Test34() {
var r0 := Min(112, 112);
expect r0 == 112 || r0 == 112;
expect r0 <= 112 && r0 <= 112;
}
method {:test} Test35() {
var r0 := Min(113, 112);
expect r0 == 113 || r0 == 112;
expect r0 <= 113 && r0 <= 112;
}

// REPEAT 9 - TIME: 18.1639313 s

method {:test} Test36() {
var r0 := Min(114, 114);
expect r0 == 114 || r0 == 114;
expect r0 <= 114 && r0 <= 114;
}
method {:test} Test37() {
var r0 := Min(114, 113);
expect r0 == 114 || r0 == 113;
expect r0 <= 114 && r0 <= 113;
}

// REPEAT 10 - TIME: 19.1248909 s
