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

method {:test} Test36() {
var r0 := Min(114, 113);
expect 114 <= 113 ==> r0 == 114;
expect 114 > 113 ==> r0 == 113;
}
method {:test} Test37() {
var r0 := Min(114, 114);
expect 114 <= 114 ==> r0 == 114;
expect 114 > 114 ==> r0 == 114;
}

// REPEAT 10 - TIME: 23.7731695 s
