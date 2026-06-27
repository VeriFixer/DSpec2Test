// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x < 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
}

method {:test} Test10() {
var r0 := Triple(48);
expect r0 == 3 * 48;
}

// REPEAT 10 - TIME: 16.4447447 s
