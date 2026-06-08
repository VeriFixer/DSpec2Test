method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test3() {
var r0 := ComputeAvg(17714, 4);
expect r0 == (17714 + 4) / 2;
}

// REPEAT 4 - TIME: 5.5610623 s
