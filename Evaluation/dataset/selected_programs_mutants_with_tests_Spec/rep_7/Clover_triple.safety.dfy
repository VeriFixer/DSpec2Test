method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test6() {
var r0 := Triple(2579);
expect r0 == 3 * 2579;
}

// REPEAT 7 - TIME: 7.7282257 s
