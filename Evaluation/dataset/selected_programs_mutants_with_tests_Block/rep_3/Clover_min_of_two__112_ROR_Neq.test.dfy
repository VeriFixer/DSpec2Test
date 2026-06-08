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

method {:test} Test4() {
var r0 := Min(3, 3);
expect 3 <= 3 ==> r0 == 3;
expect 3 > 3 ==> r0 == 3;
}
method {:test} Test5() {
var r0 := Min(3, 4);
expect 3 <= 4 ==> r0 == 3;
expect 3 > 4 ==> r0 == 4;
}

// REPEAT 3 - TIME: 4.1513518 s
