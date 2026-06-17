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

method {:test} Test16() {
var r0 := Min(12, 12);
expect 12 <= 12 ==> r0 == 12;
expect 12 > 12 ==> r0 == 12;
}
method {:test} Test17() {
var r0 := Min(12, 13);
expect 12 <= 13 ==> r0 == 12;
expect 12 > 13 ==> r0 == 13;
}

// REPEAT 9 - TIME: 10.1167884 s
