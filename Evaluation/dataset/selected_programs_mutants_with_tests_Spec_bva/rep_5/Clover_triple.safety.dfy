method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test9() {
var r0 := Triple(2577);
expect r0 == 3 * 2577;
}

// REPEAT 5 - TIME: 8.4524616 s
