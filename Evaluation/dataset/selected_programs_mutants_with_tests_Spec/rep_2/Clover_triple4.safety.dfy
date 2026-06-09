method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test1() {
var r0 := Triple(2574);
expect r0 == 3 * 2574;
}

// REPEAT 2 - TIME: 3.1494251 s
