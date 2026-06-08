method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 10 - TIME: 7.3484776 s
