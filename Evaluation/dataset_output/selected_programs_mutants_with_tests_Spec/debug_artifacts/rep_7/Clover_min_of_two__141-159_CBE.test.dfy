// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  return y;
}

method {:test} Test12() {
var r0 := Min(10, 9);
expect 10 <= 9 ==> r0 == 10;
expect 10 > 9 ==> r0 == 9;
}
method {:test} Test13() {
var r0 := Min(9, 9);
expect 9 <= 9 ==> r0 == 9;
expect 9 > 9 ==> r0 == 9;
}

// REPEAT 7 - TIME: 10.4995693 s
