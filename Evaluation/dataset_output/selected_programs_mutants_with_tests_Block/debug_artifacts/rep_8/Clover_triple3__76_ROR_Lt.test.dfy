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

method {:test} Test14() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 8 - TIME: 8.4510538 s
