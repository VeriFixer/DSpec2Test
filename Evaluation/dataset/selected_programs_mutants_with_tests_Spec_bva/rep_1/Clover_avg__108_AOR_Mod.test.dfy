// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := (a + b) % 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 1);
expect r0 == (0 + 1) / 2;
}
method {:test} Test1() {
var r0 := ComputeAvg(-100, 101);
expect r0 == (-100 + 101) / 2;
}
method {:test} Test2() {
var r0 := ComputeAvg(100, -100);
expect r0 == (100 + -100) / 2;
}
method {:test} Test3() {
var r0 := ComputeAvg(101, -100);
expect r0 == (101 + -100) / 2;
}
method {:test} Test4() {
var r0 := ComputeAvg(-100, 100);
expect r0 == (-100 + 100) / 2;
}
method {:test} Test6() {
var r0 := ComputeAvg(-200, 0);
expect r0 == (-200 + 0) / 2;
}
method {:test} Test7() {
var r0 := ComputeAvg(200, 0);
expect r0 == (200 + 0) / 2;
}
method {:test} Test8() {
var r0 := ComputeAvg(0, 1236);
expect r0 == (0 + 1236) / 2;
}
method {:test} Test9() {
var r0 := ComputeAvg(0, 0);
expect r0 == (0 + 0) / 2;
}

// REPEAT 1 - TIME: 6.1072666 s
