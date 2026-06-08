method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test5() {
var r0 := ComputeAvg(4882, 8);
expect r0 == (4882 + 8) / 2;
}

// REPEAT 6 - TIME: 7.6729627 s
