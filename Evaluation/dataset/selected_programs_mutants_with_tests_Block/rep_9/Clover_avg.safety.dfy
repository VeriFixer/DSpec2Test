method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test8() {
var r0 := ComputeAvg(17720, 10);
expect r0 == (17720 + 10) / 2;
}

// REPEAT 9 - TIME: 6.7291634 s
