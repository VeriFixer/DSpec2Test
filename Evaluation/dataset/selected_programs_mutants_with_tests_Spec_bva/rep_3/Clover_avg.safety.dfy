method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test11() {
var r0 := ComputeAvg(204, 1240);
expect r0 == (204 + 1240) / 2;
}

// REPEAT 3 - TIME: 7.4935611 s
