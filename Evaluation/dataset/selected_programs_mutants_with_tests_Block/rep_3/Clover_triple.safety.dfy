method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 3 - TIME: 3.1505963 s
