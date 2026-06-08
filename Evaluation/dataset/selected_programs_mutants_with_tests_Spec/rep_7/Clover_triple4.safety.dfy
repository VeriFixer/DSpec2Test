method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test6() {
var r0 := Triple(2579);
expect r0 == 3 * 2579;
}

// REPEAT 7 - TIME: 7.6800495 s
