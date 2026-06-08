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

method {:test} Test32() {
var r0 := Min(111, 110);
expect 111 <= 110 ==> r0 == 111;
expect 111 > 110 ==> r0 == 110;
}
method {:test} Test33() {
var r0 := Min(111, 111);
expect 111 <= 111 ==> r0 == 111;
expect 111 > 111 ==> r0 == 111;
}

// REPEAT 8 - TIME: 26.3280323 s
