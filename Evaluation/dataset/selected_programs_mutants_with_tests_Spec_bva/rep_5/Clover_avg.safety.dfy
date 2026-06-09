method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test13() {
var r0 := ComputeAvg(208, 1244);
expect r0 == (208 + 1244) / 2;
}

// REPEAT 5 - TIME: 8.8501118 s
