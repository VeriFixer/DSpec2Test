method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test10() {
var r0 := ComputeAvg(202, 1238);
expect r0 == (202 + 1238) / 2;
}

// REPEAT 2 - TIME: 7.0059772 s
