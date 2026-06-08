method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 9 - TIME: 11.7154271 s
