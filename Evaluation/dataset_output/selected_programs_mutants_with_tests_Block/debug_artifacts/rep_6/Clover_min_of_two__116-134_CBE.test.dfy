// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  return x;
}

method {:test} Test10() {
var r0 := Min(8, 8);
expect 8 <= 8 ==> r0 == 8;
expect 8 > 8 ==> r0 == 8;
}
method {:test} Test11() {
var r0 := Min(7, 8);
expect 7 <= 8 ==> r0 == 7;
expect 7 > 8 ==> r0 == 8;
}

// REPEAT 6 - TIME: 7.2894512 s
