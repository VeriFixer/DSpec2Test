// Clover_triple.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := 0;
}

method {:test} Test0() {
var r0 := Triple(38);
expect r0 == 3 * 38;
}

// REPEAT 1 - TIME: 1.983868 s
