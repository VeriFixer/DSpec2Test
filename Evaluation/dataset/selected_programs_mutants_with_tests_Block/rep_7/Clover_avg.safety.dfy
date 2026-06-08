method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test6() {
var r0 := ComputeAvg(17718, 8);
expect r0 == (17718 + 8) / 2;
}

// REPEAT 7 - TIME: 5.7245366 s
