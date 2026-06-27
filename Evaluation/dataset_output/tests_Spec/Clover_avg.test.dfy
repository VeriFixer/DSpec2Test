method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 1);
expect r0 == (0 + 1) / 2;
}

// REPEAT 1 - TIME: 2.5557111 s

method {:test} Test1() {
var r0 := ComputeAvg(4876, 2);
expect r0 == (4876 + 2) / 2;
}

// REPEAT 2 - TIME: 3.4215241 s

method {:test} Test2() {
var r0 := ComputeAvg(4877, 3);
expect r0 == (4877 + 3) / 2;
}

// REPEAT 3 - TIME: 4.4132688 s

method {:test} Test3() {
var r0 := ComputeAvg(4878, 4);
expect r0 == (4878 + 4) / 2;
}

// REPEAT 4 - TIME: 5.3027111 s

method {:test} Test4() {
var r0 := ComputeAvg(4880, 6);
expect r0 == (4880 + 6) / 2;
}

// REPEAT 5 - TIME: 6.166437 s

method {:test} Test5() {
var r0 := ComputeAvg(4882, 8);
expect r0 == (4882 + 8) / 2;
}

// REPEAT 6 - TIME: 7.065119 s

method {:test} Test6() {
var r0 := ComputeAvg(4884, 10);
expect r0 == (4884 + 10) / 2;
}

// REPEAT 7 - TIME: 8.0524499 s

method {:test} Test7() {
var r0 := ComputeAvg(4886, 12);
expect r0 == (4886 + 12) / 2;
}

// REPEAT 8 - TIME: 9.1283136 s

method {:test} Test8() {
var r0 := ComputeAvg(4888, 14);
expect r0 == (4888 + 14) / 2;
}

// REPEAT 9 - TIME: 10.0151096 s

method {:test} Test9() {
var r0 := ComputeAvg(4890, 16);
expect r0 == (4890 + 16) / 2;
}

// REPEAT 10 - TIME: 10.8054801 s
