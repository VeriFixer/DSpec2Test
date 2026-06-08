method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test5() {
var r0 := Triple(2578);
expect r0 == 3 * 2578;
}

// REPEAT 6 - TIME: 7.1045675 s
