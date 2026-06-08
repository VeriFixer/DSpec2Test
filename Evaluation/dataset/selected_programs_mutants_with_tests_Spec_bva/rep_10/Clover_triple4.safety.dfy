method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test14() {
var r0 := Triple(2582);
expect r0 == 3 * 2582;
}

// REPEAT 10 - TIME: 11.5932635 s
