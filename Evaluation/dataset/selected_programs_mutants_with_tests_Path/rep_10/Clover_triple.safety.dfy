method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 10 - TIME: 7.2260687 s
