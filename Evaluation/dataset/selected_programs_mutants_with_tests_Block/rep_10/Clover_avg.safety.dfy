method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test9() {
var r0 := ComputeAvg(17722, 12);
expect r0 == (17722 + 12) / 2;
}

// REPEAT 10 - TIME: 7.368479 s
