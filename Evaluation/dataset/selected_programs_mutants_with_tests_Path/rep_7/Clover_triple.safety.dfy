method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 7 - TIME: 5.4421325 s
