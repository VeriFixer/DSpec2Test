// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a <= b <==> a <= c {
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
var r0 := MinOfThree(-100, 0, 0);
expect r0 <= -100 && r0 <= 0 && r0 <= 0;
expect r0 == -100 || r0 == 0 || r0 == 0;
}
method {:test} Test2() {
var r0 := MinOfThree(100, 100, 100);
expect r0 <= 100 && r0 <= 100 && r0 <= 100;
expect r0 == 100 || r0 == 100 || r0 == 100;
}
method {:test} Test3() {
var r0 := MinOfThree(-100, -100, 0);
expect r0 <= -100 && r0 <= -100 && r0 <= 0;
expect r0 == -100 || r0 == -100 || r0 == 0;
}
method {:test} Test4() {
var r0 := MinOfThree(0, 100, 0);
expect r0 <= 0 && r0 <= 100 && r0 <= 0;
expect r0 == 0 || r0 == 100 || r0 == 0;
}
method {:test} Test5() {
var r0 := MinOfThree(-100, 0, -100);
expect r0 <= -100 && r0 <= 0 && r0 <= -100;
expect r0 == -100 || r0 == 0 || r0 == -100;
}
method {:test} Test6() {
var r0 := MinOfThree(0, 0, 100);
expect r0 <= 0 && r0 <= 0 && r0 <= 100;
expect r0 == 0 || r0 == 0 || r0 == 100;
}
method {:test} Test12() {
var r0 := MinOfThree(1, 0, 0);
expect r0 <= 1 && r0 <= 0 && r0 <= 0;
expect r0 == 1 || r0 == 0 || r0 == 0;
}
method {:test} Test13() {
var r0 := MinOfThree(-100, -101, 0);
expect r0 <= -100 && r0 <= -101 && r0 <= 0;
expect r0 == -100 || r0 == -101 || r0 == 0;
}
method {:test} Test14() {
var r0 := MinOfThree(100, 0, 0);
expect r0 <= 100 && r0 <= 0 && r0 <= 0;
expect r0 == 100 || r0 == 0 || r0 == 0;
}
method {:test} Test15() {
var r0 := MinOfThree(0, -100, 0);
expect r0 <= 0 && r0 <= -100 && r0 <= 0;
expect r0 == 0 || r0 == -100 || r0 == 0;
}
method {:test} Test16() {
var r0 := MinOfThree(101, 100, 100);
expect r0 <= 101 && r0 <= 100 && r0 <= 100;
expect r0 == 101 || r0 == 100 || r0 == 100;
}
method {:test} Test17() {
var r0 := MinOfThree(0, -100, -100);
expect r0 <= 0 && r0 <= -100 && r0 <= -100;
expect r0 == 0 || r0 == -100 || r0 == -100;
}
method {:test} Test18() {
var r0 := MinOfThree(1, 0, 100);
expect r0 <= 1 && r0 <= 0 && r0 <= 100;
expect r0 == 1 || r0 == 0 || r0 == 100;
}
method {:test} Test24() {
var r0 := MinOfThree(1, 1, 0);
expect r0 <= 1 && r0 <= 1 && r0 <= 0;
expect r0 == 1 || r0 == 1 || r0 == 0;
}
method {:test} Test25() {
var r0 := MinOfThree(-100, 0, -101);
expect r0 <= -100 && r0 <= 0 && r0 <= -101;
expect r0 == -100 || r0 == 0 || r0 == -101;
}
method {:test} Test26() {
var r0 := MinOfThree(100, 1, 0);
expect r0 <= 100 && r0 <= 1 && r0 <= 0;
expect r0 == 100 || r0 == 1 || r0 == 0;
}
method {:test} Test27() {
var r0 := MinOfThree(0, -100, -101);
expect r0 <= 0 && r0 <= -100 && r0 <= -101;
expect r0 == 0 || r0 == -100 || r0 == -101;
}
method {:test} Test28() {
var r0 := MinOfThree(1, 100, 0);
expect r0 <= 1 && r0 <= 100 && r0 <= 0;
expect r0 == 1 || r0 == 100 || r0 == 0;
}
method {:test} Test29() {
var r0 := MinOfThree(0, 0, -100);
expect r0 <= 0 && r0 <= 0 && r0 <= -100;
expect r0 == 0 || r0 == 0 || r0 == -100;
}
method {:test} Test30() {
var r0 := MinOfThree(101, 101, 100);
expect r0 <= 101 && r0 <= 101 && r0 <= 100;
expect r0 == 101 || r0 == 101 || r0 == 100;
}

// REPEAT 1 - TIME: 21.0182881 s

method {:test} Test36() {
var r0 := MinOfThree(102, 102, 102);
expect r0 <= 102 && r0 <= 102 && r0 <= 102;
expect r0 == 102 || r0 == 102 || r0 == 102;
}
method {:test} Test37() {
var r0 := MinOfThree(103, 102, 102);
expect r0 <= 103 && r0 <= 102 && r0 <= 102;
expect r0 == 103 || r0 == 102 || r0 == 102;
}
method {:test} Test38() {
var r0 := MinOfThree(102, 102, 101);
expect r0 <= 102 && r0 <= 102 && r0 <= 101;
expect r0 == 102 || r0 == 102 || r0 == 101;
}

// REPEAT 2 - TIME: 23.0044553 s

method {:test} Test39() {
var r0 := MinOfThree(104, 104, 104);
expect r0 <= 104 && r0 <= 104 && r0 <= 104;
expect r0 == 104 || r0 == 104 || r0 == 104;
}
method {:test} Test40() {
var r0 := MinOfThree(104, 103, 103);
expect r0 <= 104 && r0 <= 103 && r0 <= 103;
expect r0 == 104 || r0 == 103 || r0 == 103;
}
method {:test} Test41() {
var r0 := MinOfThree(104, 104, 103);
expect r0 <= 104 && r0 <= 104 && r0 <= 103;
expect r0 == 104 || r0 == 104 || r0 == 103;
}

// REPEAT 3 - TIME: 24.5654105 s

method {:test} Test42() {
var r0 := MinOfThree(105, 105, 105);
expect r0 <= 105 && r0 <= 105 && r0 <= 105;
expect r0 == 105 || r0 == 105 || r0 == 105;
}
method {:test} Test43() {
var r0 := MinOfThree(106, 105, 105);
expect r0 <= 106 && r0 <= 105 && r0 <= 105;
expect r0 == 106 || r0 == 105 || r0 == 105;
}
method {:test} Test44() {
var r0 := MinOfThree(106, 106, 105);
expect r0 <= 106 && r0 <= 106 && r0 <= 105;
expect r0 == 106 || r0 == 106 || r0 == 105;
}

// REPEAT 4 - TIME: 25.8950773 s

method {:test} Test45() {
var r0 := MinOfThree(107, 107, 107);
expect r0 <= 107 && r0 <= 107 && r0 <= 107;
expect r0 == 107 || r0 == 107 || r0 == 107;
}
method {:test} Test46() {
var r0 := MinOfThree(108, 107, 107);
expect r0 <= 108 && r0 <= 107 && r0 <= 107;
expect r0 == 108 || r0 == 107 || r0 == 107;
}
method {:test} Test47() {
var r0 := MinOfThree(107, 107, 106);
expect r0 <= 107 && r0 <= 107 && r0 <= 106;
expect r0 == 107 || r0 == 107 || r0 == 106;
}

// REPEAT 5 - TIME: 27.4215134 s

method {:test} Test48() {
var r0 := MinOfThree(109, 109, 109);
expect r0 <= 109 && r0 <= 109 && r0 <= 109;
expect r0 == 109 || r0 == 109 || r0 == 109;
}
method {:test} Test49() {
var r0 := MinOfThree(109, 108, 108);
expect r0 <= 109 && r0 <= 108 && r0 <= 108;
expect r0 == 109 || r0 == 108 || r0 == 108;
}
method {:test} Test50() {
var r0 := MinOfThree(109, 109, 108);
expect r0 <= 109 && r0 <= 109 && r0 <= 108;
expect r0 == 109 || r0 == 109 || r0 == 108;
}

// REPEAT 6 - TIME: 28.8762507 s

method {:test} Test51() {
var r0 := MinOfThree(110, 110, 110);
expect r0 <= 110 && r0 <= 110 && r0 <= 110;
expect r0 == 110 || r0 == 110 || r0 == 110;
}
method {:test} Test52() {
var r0 := MinOfThree(111, 110, 110);
expect r0 <= 111 && r0 <= 110 && r0 <= 110;
expect r0 == 111 || r0 == 110 || r0 == 110;
}
method {:test} Test53() {
var r0 := MinOfThree(111, 111, 110);
expect r0 <= 111 && r0 <= 111 && r0 <= 110;
expect r0 == 111 || r0 == 111 || r0 == 110;
}

// REPEAT 7 - TIME: 30.5705156 s

method {:test} Test54() {
var r0 := MinOfThree(112, 112, 112);
expect r0 <= 112 && r0 <= 112 && r0 <= 112;
expect r0 == 112 || r0 == 112 || r0 == 112;
}
method {:test} Test55() {
var r0 := MinOfThree(113, 112, 112);
expect r0 <= 113 && r0 <= 112 && r0 <= 112;
expect r0 == 113 || r0 == 112 || r0 == 112;
}
method {:test} Test56() {
var r0 := MinOfThree(112, 112, 111);
expect r0 <= 112 && r0 <= 112 && r0 <= 111;
expect r0 == 112 || r0 == 112 || r0 == 111;
}

// REPEAT 8 - TIME: 32.282042 s

method {:test} Test57() {
var r0 := MinOfThree(114, 114, 114);
expect r0 <= 114 && r0 <= 114 && r0 <= 114;
expect r0 == 114 || r0 == 114 || r0 == 114;
}
method {:test} Test58() {
var r0 := MinOfThree(114, 113, 113);
expect r0 <= 114 && r0 <= 113 && r0 <= 113;
expect r0 == 114 || r0 == 113 || r0 == 113;
}
method {:test} Test59() {
var r0 := MinOfThree(114, 114, 113);
expect r0 <= 114 && r0 <= 114 && r0 <= 113;
expect r0 == 114 || r0 == 114 || r0 == 113;
}

// REPEAT 9 - TIME: 34.2286319 s

method {:test} Test60() {
var r0 := MinOfThree(115, 115, 115);
expect r0 <= 115 && r0 <= 115 && r0 <= 115;
expect r0 == 115 || r0 == 115 || r0 == 115;
}
method {:test} Test61() {
var r0 := MinOfThree(116, 115, 115);
expect r0 <= 116 && r0 <= 115 && r0 <= 115;
expect r0 == 116 || r0 == 115 || r0 == 115;
}
method {:test} Test62() {
var r0 := MinOfThree(116, 116, 115);
expect r0 <= 116 && r0 <= 116 && r0 <= 115;
expect r0 == 116 || r0 == 116 || r0 == 115;
}

// REPEAT 10 - TIME: 35.9581279 s
