method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test7() {
var r0 := Triple(2575);
expect r0 == 3 * 2575;
}

// REPEAT 3 - TIME: 5.9150478 s
