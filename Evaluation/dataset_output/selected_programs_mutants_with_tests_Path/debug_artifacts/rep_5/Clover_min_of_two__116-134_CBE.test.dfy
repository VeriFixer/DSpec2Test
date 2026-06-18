// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  return x;
}

method {:test} Test8() {
var r0 := Min(6, 7);
expect 6 <= 7 ==> r0 == 6;
expect 6 > 7 ==> r0 == 7;
}
method {:test} Test9() {
var r0 := Min(6, 6);
expect 6 <= 6 ==> r0 == 6;
expect 6 > 6 ==> r0 == 6;
}

// REPEAT 5 - TIME: 13.3853414 s
