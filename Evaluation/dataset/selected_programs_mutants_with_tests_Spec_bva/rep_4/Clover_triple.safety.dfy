method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test8() {
var r0 := Triple(2576);
expect r0 == 3 * 2576;
}

// REPEAT 4 - TIME: 7.6885066 s
