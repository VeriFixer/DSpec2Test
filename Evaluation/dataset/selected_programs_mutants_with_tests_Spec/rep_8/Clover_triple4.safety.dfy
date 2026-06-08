method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test7() {
var r0 := Triple(2580);
expect r0 == 3 * 2580;
}

// REPEAT 8 - TIME: 8.3689661 s
