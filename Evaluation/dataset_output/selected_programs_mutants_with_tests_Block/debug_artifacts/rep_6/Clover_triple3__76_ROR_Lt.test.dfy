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
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 6 - TIME: 7.8291875 s
