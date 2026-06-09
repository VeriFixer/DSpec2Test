method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 4 - TIME: 6.1370231 s
