// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if x != y {
    return x;
  } else {
    return y;
  }
}

method {:test} Test18() {
var r0 := Min(13, 14);
expect 13 <= 14 ==> r0 == 13;
expect 13 > 14 ==> r0 == 14;
}
method {:test} Test19() {
var r0 := Min(14, 14);
expect 14 <= 14 ==> r0 == 14;
expect 14 > 14 ==> r0 == 14;
}

// REPEAT 10 - TIME: 17.2997343 s
