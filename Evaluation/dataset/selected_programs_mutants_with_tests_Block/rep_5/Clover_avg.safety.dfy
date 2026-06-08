method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test4() {
var r0 := ComputeAvg(17715, 5);
expect r0 == (17715 + 5) / 2;
}

// REPEAT 5 - TIME: 4.4460402 s
