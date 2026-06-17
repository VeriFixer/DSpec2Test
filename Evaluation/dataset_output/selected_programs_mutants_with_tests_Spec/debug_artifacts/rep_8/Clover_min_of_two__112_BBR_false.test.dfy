// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if false {
    return x;
  } else {
    return y;
  }
}

method {:test} Test14() {
var r0 := Min(11, 10);
expect 11 <= 10 ==> r0 == 11;
expect 11 > 10 ==> r0 == 10;
}
method {:test} Test15() {
var r0 := Min(11, 11);
expect 11 <= 11 ==> r0 == 11;
expect 11 > 11 ==> r0 == 11;
}

// REPEAT 8 - TIME: 15.5516353 s
