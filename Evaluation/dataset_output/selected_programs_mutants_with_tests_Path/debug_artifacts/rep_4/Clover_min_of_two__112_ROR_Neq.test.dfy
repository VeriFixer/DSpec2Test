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

method {:test} Test6() {
var r0 := Min(4, 5);
expect 4 <= 5 ==> r0 == 4;
expect 4 > 5 ==> r0 == 5;
}
method {:test} Test7() {
var r0 := Min(5, 5);
expect 5 <= 5 ==> r0 == 5;
expect 5 > 5 ==> r0 == 5;
}

// REPEAT 4 - TIME: 6.951299 s
