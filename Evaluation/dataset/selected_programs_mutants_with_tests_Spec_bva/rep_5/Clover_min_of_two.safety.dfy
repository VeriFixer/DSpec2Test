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

method {:test} Test26() {
var r0 := Min(107, 106);
expect 107 <= 106 ==> r0 == 107;
expect 107 > 106 ==> r0 == 106;
}
method {:test} Test27() {
var r0 := Min(106, 106);
expect 106 <= 106 ==> r0 == 106;
expect 106 > 106 ==> r0 == 106;
}

// REPEAT 5 - TIME: 21.9314486 s
