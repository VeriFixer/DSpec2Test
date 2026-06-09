method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test6() {
var r0 := ComputeAvg(4884, 10);
expect r0 == (4884 + 10) / 2;
}

// REPEAT 7 - TIME: 6.8227367 s
