method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 7 - TIME: 5.7485454 s
