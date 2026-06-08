method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test5() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 6 - TIME: 5.1850232 s
