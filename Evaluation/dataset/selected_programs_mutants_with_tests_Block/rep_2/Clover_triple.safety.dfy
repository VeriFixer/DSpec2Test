method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test1() {
var r0 := Triple(39);
expect r0 == 3 * 39;
}

// REPEAT 2 - TIME: 2.5468295 s
