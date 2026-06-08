method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test4() {
var r0 := Triple(2577);
expect r0 == 3 * 2577;
}

// REPEAT 5 - TIME: 6.0497582 s
