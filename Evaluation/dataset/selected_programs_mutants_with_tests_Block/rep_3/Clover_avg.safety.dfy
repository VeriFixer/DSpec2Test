method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test2() {
var r0 := ComputeAvg(17713, 3);
expect r0 == (17713 + 3) / 2;
}

// REPEAT 3 - TIME: 3.1905717 s
