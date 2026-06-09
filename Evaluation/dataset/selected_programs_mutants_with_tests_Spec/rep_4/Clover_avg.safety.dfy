method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test3() {
var r0 := ComputeAvg(4878, 4);
expect r0 == (4878 + 4) / 2;
}

// REPEAT 4 - TIME: 4.4026827 s
