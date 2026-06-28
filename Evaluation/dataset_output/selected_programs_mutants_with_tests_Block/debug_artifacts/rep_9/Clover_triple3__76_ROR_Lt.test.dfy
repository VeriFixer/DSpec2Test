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

method {:test} Test16() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 9 - TIME: 9.1568347 s
