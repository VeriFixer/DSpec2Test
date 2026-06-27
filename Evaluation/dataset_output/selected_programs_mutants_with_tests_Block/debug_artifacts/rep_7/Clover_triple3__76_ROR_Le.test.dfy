// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x <= 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
}

method {:test} Test12() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 7 - TIME: 8.8138617 s
