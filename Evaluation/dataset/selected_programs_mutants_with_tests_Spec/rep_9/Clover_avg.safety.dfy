method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test8() {
var r0 := ComputeAvg(4888, 14);
expect r0 == (4888 + 14) / 2;
}

// REPEAT 9 - TIME: 8.2841479 s
