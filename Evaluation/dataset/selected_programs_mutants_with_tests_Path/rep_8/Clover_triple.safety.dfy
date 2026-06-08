method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test7() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 8 - TIME: 10.8228457 s
