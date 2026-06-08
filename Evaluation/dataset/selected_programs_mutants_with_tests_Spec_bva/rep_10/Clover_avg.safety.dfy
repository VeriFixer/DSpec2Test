method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test18() {
var r0 := ComputeAvg(218, 1254);
expect r0 == (218 + 1254) / 2;
}

// REPEAT 10 - TIME: 12.7259948 s
