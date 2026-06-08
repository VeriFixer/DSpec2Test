method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test15() {
var r0 := ComputeAvg(212, 1248);
expect r0 == (212 + 1248) / 2;
}

// REPEAT 7 - TIME: 10.7847288 s
