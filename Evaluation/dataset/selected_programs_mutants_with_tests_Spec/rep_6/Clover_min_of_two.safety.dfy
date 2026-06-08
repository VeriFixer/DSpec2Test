method {:testEntry} Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{
  if x < y {
    return x;
  } else {
    return y;
  }
}

method {:test} Test10() {
var r0 := Min(8, 7);
expect 8 <= 7 ==> r0 == 8;
expect 8 > 7 ==> r0 == 7;
}
method {:test} Test11() {
var r0 := Min(8, 8);
expect 8 <= 8 ==> r0 == 8;
expect 8 > 8 ==> r0 == 8;
}

// REPEAT 6 - TIME: 12.6708075 s
