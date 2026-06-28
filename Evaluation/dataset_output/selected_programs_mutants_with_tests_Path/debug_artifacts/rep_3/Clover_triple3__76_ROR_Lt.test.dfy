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

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 3 - TIME: 9.1142788 s
