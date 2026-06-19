// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if false {
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
var r0 := Min(-100, -101);
expect -100 <= -101 ==> r0 == -100;
expect -100 > -101 ==> r0 == -101;
}
method {:test} Test2() {
var r0 := Min(100, 0);
expect 100 <= 0 ==> r0 == 100;
expect 100 > 0 ==> r0 == 0;
}
method {:test} Test3() {
var r0 := Min(0, -100);
expect 0 <= -100 ==> r0 == 0;
expect 0 > -100 ==> r0 == -100;
}
method {:test} Test4() {
var r0 := Min(101, 100);
expect 101 <= 100 ==> r0 == 101;
expect 101 > 100 ==> r0 == 100;
}
method {:test} Test10() {
var r0 := Min(0, 0);
expect 0 <= 0 ==> r0 == 0;
expect 0 > 0 ==> r0 == 0;
}
method {:test} Test11() {
var r0 := Min(-100, 0);
expect -100 <= 0 ==> r0 == -100;
expect -100 > 0 ==> r0 == 0;
}
method {:test} Test12() {
var r0 := Min(100, 100);
expect 100 <= 100 ==> r0 == 100;
expect 100 > 100 ==> r0 == 100;
}
method {:test} Test13() {
var r0 := Min(-100, -100);
expect -100 <= -100 ==> r0 == -100;
expect -100 > -100 ==> r0 == -100;
}
method {:test} Test14() {
var r0 := Min(0, 100);
expect 0 <= 100 ==> r0 == 0;
expect 0 > 100 ==> r0 == 100;
}

// REPEAT 1 - TIME: 16.8978675 s

method {:test} Test20() {
var r0 := Min(102, 101);
expect 102 <= 101 ==> r0 == 102;
expect 102 > 101 ==> r0 == 101;
}
method {:test} Test21() {
var r0 := Min(102, 102);
expect 102 <= 102 ==> r0 == 102;
expect 102 > 102 ==> r0 == 102;
}

// REPEAT 2 - TIME: 18.3701047 s

method {:test} Test22() {
var r0 := Min(104, 103);
expect 104 <= 103 ==> r0 == 104;
expect 104 > 103 ==> r0 == 103;
}
method {:test} Test23() {
var r0 := Min(103, 103);
expect 103 <= 103 ==> r0 == 103;
expect 103 > 103 ==> r0 == 103;
}

// REPEAT 3 - TIME: 19.7911415 s

method {:test} Test24() {
var r0 := Min(105, 104);
expect 105 <= 104 ==> r0 == 105;
expect 105 > 104 ==> r0 == 104;
}
method {:test} Test25() {
var r0 := Min(105, 105);
expect 105 <= 105 ==> r0 == 105;
expect 105 > 105 ==> r0 == 105;
}

// REPEAT 4 - TIME: 21.2989146 s

method {:test} Test26() {
var r0 := Min(107, 106);
expect 107 <= 106 ==> r0 == 107;
expect 107 > 106 ==> r0 == 106;
}
method {:test} Test27() {
var r0 := Min(106, 106);
expect 106 <= 106 ==> r0 == 106;
expect 106 > 106 ==> r0 == 106;
}

// REPEAT 5 - TIME: 22.8455822 s

method {:test} Test28() {
var r0 := Min(108, 107);
expect 108 <= 107 ==> r0 == 108;
expect 108 > 107 ==> r0 == 107;
}
method {:test} Test29() {
var r0 := Min(108, 108);
expect 108 <= 108 ==> r0 == 108;
expect 108 > 108 ==> r0 == 108;
}

// REPEAT 6 - TIME: 24.4482915 s

method {:test} Test30() {
var r0 := Min(110, 109);
expect 110 <= 109 ==> r0 == 110;
expect 110 > 109 ==> r0 == 109;
}
method {:test} Test31() {
var r0 := Min(109, 109);
expect 109 <= 109 ==> r0 == 109;
expect 109 > 109 ==> r0 == 109;
}

// REPEAT 7 - TIME: 25.866403 s

method {:test} Test32() {
var r0 := Min(111, 110);
expect 111 <= 110 ==> r0 == 111;
expect 111 > 110 ==> r0 == 110;
}
method {:test} Test33() {
var r0 := Min(111, 111);
expect 111 <= 111 ==> r0 == 111;
expect 111 > 111 ==> r0 == 111;
}

// REPEAT 8 - TIME: 27.3549825 s

method {:test} Test34() {
var r0 := Min(113, 112);
expect 113 <= 112 ==> r0 == 113;
expect 113 > 112 ==> r0 == 112;
}
method {:test} Test35() {
var r0 := Min(112, 112);
expect 112 <= 112 ==> r0 == 112;
expect 112 > 112 ==> r0 == 112;
}

// REPEAT 9 - TIME: 28.7242476 s

method {:test} Test36() {
var r0 := Min(114, 113);
expect 114 <= 113 ==> r0 == 114;
expect 114 > 113 ==> r0 == 113;
}
method {:test} Test37() {
var r0 := Min(114, 114);
expect 114 <= 114 ==> r0 == 114;
expect 114 > 114 ==> r0 == 114;
}

// REPEAT 10 - TIME: 29.9945471 s
