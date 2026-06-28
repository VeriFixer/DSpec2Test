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

method {:test} Test8() {
var r0 := Triple(2581);
expect r0 == 3 * 2581;
}

// REPEAT 9 - TIME: 10.2276449 s
