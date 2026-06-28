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

method {:test} Test9() {
var r0 := Triple(2582);
expect r0 == 3 * 2582;
}

// REPEAT 10 - TIME: 11.1574322 s
