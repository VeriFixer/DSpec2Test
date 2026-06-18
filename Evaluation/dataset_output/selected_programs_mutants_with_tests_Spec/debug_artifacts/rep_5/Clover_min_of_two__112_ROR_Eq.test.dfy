// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if x == y {
    return x;
  } else {
    return y;
  }
}

method {:test} Test8() {
var r0 := Min(7, 6);
expect 7 <= 6 ==> r0 == 7;
expect 7 > 6 ==> r0 == 6;
}
method {:test} Test9() {
var r0 := Min(6, 6);
expect 6 <= 6 ==> r0 == 6;
expect 6 > 6 ==> r0 == 6;
}

// REPEAT 5 - TIME: 10.7413323 s
