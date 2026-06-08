method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 4 - TIME: 3.8548933 s
