method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test1() {
var r0 := Triple(39);
expect r0 == 3 * 39;
}

// REPEAT 2 - TIME: 4.4292127 s
