// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := a + b - 2;
}


method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 1);
expect r0 == (0 + 1) / 2;
}

// REPEAT 1 - TIME: 2.3318166 s

method {:test} Test1() {
var r0 := ComputeAvg(4876, 2);
expect r0 == (4876 + 2) / 2;
}

// REPEAT 2 - TIME: 3.2019357 s

method {:test} Test2() {
var r0 := ComputeAvg(4877, 3);
expect r0 == (4877 + 3) / 2;
}

// REPEAT 3 - TIME: 4.1682548 s

method {:test} Test3() {
var r0 := ComputeAvg(4878, 4);
expect r0 == (4878 + 4) / 2;
}

// REPEAT 4 - TIME: 5.1946809 s

method {:test} Test4() {
var r0 := ComputeAvg(4880, 6);
expect r0 == (4880 + 6) / 2;
}

// REPEAT 5 - TIME: 6.0360855 s

method {:test} Test5() {
var r0 := ComputeAvg(4882, 8);
expect r0 == (4882 + 8) / 2;
}

// REPEAT 6 - TIME: 6.9184294 s

method {:test} Test6() {
var r0 := ComputeAvg(4884, 10);
expect r0 == (4884 + 10) / 2;
}

// REPEAT 7 - TIME: 7.7470837 s

method {:test} Test7() {
var r0 := ComputeAvg(4886, 12);
expect r0 == (4886 + 12) / 2;
}

// REPEAT 8 - TIME: 8.596708 s

method {:test} Test8() {
var r0 := ComputeAvg(4888, 14);
expect r0 == (4888 + 14) / 2;
}

// REPEAT 9 - TIME: 9.2426892 s

method {:test} Test9() {
var r0 := ComputeAvg(4890, 16);
expect r0 == (4890 + 16) / 2;
}

// REPEAT 10 - TIME: 9.9702556 s
