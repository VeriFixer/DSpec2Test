method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test16() {
var r0 := ComputeAvg(214, 1250);
expect r0 == (214 + 1250) / 2;
}

// REPEAT 8 - TIME: 10.7822048 s
