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

method {:test} Test34() {
var r0 := Min(113, 112);
expect 113 <= 112 ==> r0 == 113;
expect 113 > 112 ==> r0 == 112;
}
method {:test} Test35() {
var r0 := Min(112, 112);
expect 112 <= 112 ==> r0 == 112;
expect 112 > 112 ==> r0 == 112;
}

// REPEAT 9 - TIME: 27.7334025 s
