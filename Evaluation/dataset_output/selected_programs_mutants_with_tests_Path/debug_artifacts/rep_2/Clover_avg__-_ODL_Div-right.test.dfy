// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := a + b;
}

method {:test} Test1() {
var r0 := ComputeAvg(17712, 2);
expect r0 == (17712 + 2) / 2;
}

// REPEAT 2 - TIME: 4.6392148 s
