method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test2() {
var r0 := ComputeAvg(4877, 3);
expect r0 == (4877 + 3) / 2;
}

// REPEAT 3 - TIME: 4.8722683 s
