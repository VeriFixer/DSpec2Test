method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test7() {
var r0 := ComputeAvg(17719, 9);
expect r0 == (17719 + 9) / 2;
}

// REPEAT 8 - TIME: 6.2394246 s
