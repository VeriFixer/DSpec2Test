// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := a * b / 2;
}

method {:test} Test1() {
var r0 := ComputeAvg(4876, 2);
expect r0 == (4876 + 2) / 2;
}

// REPEAT 2 - TIME: 2.7489799 s
