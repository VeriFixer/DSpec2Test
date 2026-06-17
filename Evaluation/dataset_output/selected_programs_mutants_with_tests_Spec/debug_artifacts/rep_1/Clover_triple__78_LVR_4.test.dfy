// Clover_triple.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := x * 4;
}

method {:test} Test0() {
var r0 := Triple(2573);
expect r0 == 3 * 2573;
}

// REPEAT 1 - TIME: 2.4967435 s
