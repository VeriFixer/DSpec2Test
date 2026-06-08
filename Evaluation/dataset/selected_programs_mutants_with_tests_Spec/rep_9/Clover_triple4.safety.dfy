method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test8() {
var r0 := Triple(2581);
expect r0 == 3 * 2581;
}

// REPEAT 9 - TIME: 8.9970052 s
