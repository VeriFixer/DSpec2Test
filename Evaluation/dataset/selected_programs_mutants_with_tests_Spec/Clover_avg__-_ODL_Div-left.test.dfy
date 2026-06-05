// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 1);
expect r0 == (0 + 1) / 2;
}

// REPEAT 1 - TIME: 1.185929 s

method {:test} Test1() {
var r0 := ComputeAvg(4876, 2);
expect r0 == (4876 + 2) / 2;
}

// REPEAT 2 - TIME: 1.5609214 s

method {:test} Test2() {
var r0 := ComputeAvg(4877, 3);
expect r0 == (4877 + 3) / 2;
}

// REPEAT 3 - TIME: 1.9405485 s

method {:test} Test3() {
var r0 := ComputeAvg(4878, 4);
expect r0 == (4878 + 4) / 2;
}

// REPEAT 4 - TIME: 2.3287277 s
