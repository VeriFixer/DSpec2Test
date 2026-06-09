method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test4() {
var r0 := ComputeAvg(4880, 6);
expect r0 == (4880 + 6) / 2;
}

// REPEAT 5 - TIME: 5.2026485 s
