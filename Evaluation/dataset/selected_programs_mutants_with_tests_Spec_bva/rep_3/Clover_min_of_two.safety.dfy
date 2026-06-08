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

method {:test} Test22() {
var r0 := Min(104, 103);
expect 104 <= 103 ==> r0 == 104;
expect 104 > 103 ==> r0 == 103;
}
method {:test} Test23() {
var r0 := Min(103, 103);
expect 103 <= 103 ==> r0 == 103;
expect 103 > 103 ==> r0 == 103;
}

// REPEAT 3 - TIME: 19.0179972 s
