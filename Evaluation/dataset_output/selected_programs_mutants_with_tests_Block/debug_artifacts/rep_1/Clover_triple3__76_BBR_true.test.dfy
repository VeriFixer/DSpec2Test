// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if true {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
}

method {:test} Test0() {
var r0 := Triple(1);
expect r0 == 3 * 1;
}
method {:test} Test1() {
var r0 := Triple(0);
expect r0 == 3 * 0;
}

// REPEAT 1 - TIME: 2.0661515 s
