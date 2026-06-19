// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if x >= y {
    return x;
  } else {
    return y;
  }
}

method {:test} Test0() {
var r0 := Min(1, 0);
expect 1 <= 0 ==> r0 == 1;
expect 1 > 0 ==> r0 == 0;
}
method {:test} Test1() {
var r0 := Min(0, 0);
expect 0 <= 0 ==> r0 == 0;
expect 0 > 0 ==> r0 == 0;
}

// REPEAT 1 - TIME: 3.4963767 s
