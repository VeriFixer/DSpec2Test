method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test4() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 5 - TIME: 7.4902823 s
