method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 3 - TIME: 5.431085 s
