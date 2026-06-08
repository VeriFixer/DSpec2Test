method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 9 - TIME: 11.8599652 s
