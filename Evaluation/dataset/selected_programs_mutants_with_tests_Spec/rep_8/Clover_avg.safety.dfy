method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test7() {
var r0 := ComputeAvg(4886, 12);
expect r0 == (4886 + 12) / 2;
}

// REPEAT 8 - TIME: 9.1413093 s
