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

method {:test} Test6() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 4 - TIME: 4.6413497 s
