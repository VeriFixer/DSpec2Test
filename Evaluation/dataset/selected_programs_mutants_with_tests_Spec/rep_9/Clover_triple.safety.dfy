method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test8() {
var r0 := Triple(2581);
expect r0 == 3 * 2581;
}

// REPEAT 9 - TIME: 9.0386926 s
