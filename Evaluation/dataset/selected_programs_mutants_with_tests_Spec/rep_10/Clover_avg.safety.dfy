method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test9() {
var r0 := ComputeAvg(4890, 16);
expect r0 == (4890 + 16) / 2;
}

// REPEAT 10 - TIME: 10.7161994 s
