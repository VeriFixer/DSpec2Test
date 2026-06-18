// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if true {
    return x;
  } else {
    return y;
  }
}

method {:test} Test8() {
var r0 := Min(6, 6);
expect 6 <= 6 ==> r0 == 6;
expect 6 > 6 ==> r0 == 6;
}
method {:test} Test9() {
var r0 := Min(6, 7);
expect 6 <= 7 ==> r0 == 6;
expect 6 > 7 ==> r0 == 7;
}

// REPEAT 5 - TIME: 6.2401991 s
