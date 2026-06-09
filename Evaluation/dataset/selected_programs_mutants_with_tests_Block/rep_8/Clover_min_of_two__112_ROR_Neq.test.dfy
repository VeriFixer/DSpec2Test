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

method {:test} Test14() {
var r0 := Min(11, 11);
expect 11 <= 11 ==> r0 == 11;
expect 11 > 11 ==> r0 == 11;
}
method {:test} Test15() {
var r0 := Min(10, 11);
expect 10 <= 11 ==> r0 == 10;
expect 10 > 11 ==> r0 == 11;
}

// REPEAT 8 - TIME: 8.4564011 s
