method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test17() {
var r0 := ComputeAvg(216, 1252);
expect r0 == (216 + 1252) / 2;
}

// REPEAT 9 - TIME: 12.1299215 s
