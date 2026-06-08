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

method {:test} Test12() {
var r0 := Min(9, 10);
expect 9 <= 10 ==> r0 == 9;
expect 9 > 10 ==> r0 == 10;
}
method {:test} Test13() {
var r0 := Min(9, 9);
expect 9 <= 9 ==> r0 == 9;
expect 9 > 9 ==> r0 == 9;
}

// REPEAT 7 - TIME: 13.508629 s
