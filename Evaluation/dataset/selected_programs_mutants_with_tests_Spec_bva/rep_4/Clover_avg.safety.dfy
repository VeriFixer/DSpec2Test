method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test12() {
var r0 := ComputeAvg(206, 1242);
expect r0 == (206 + 1242) / 2;
}

// REPEAT 4 - TIME: 8.2227412 s
