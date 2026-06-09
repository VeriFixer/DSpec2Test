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

method {:test} Test30() {
var r0 := Min(110, 109);
expect 110 <= 109 ==> r0 == 110;
expect 110 > 109 ==> r0 == 109;
}
method {:test} Test31() {
var r0 := Min(109, 109);
expect 109 <= 109 ==> r0 == 109;
expect 109 > 109 ==> r0 == 109;
}

// REPEAT 7 - TIME: 20.2468825 s
