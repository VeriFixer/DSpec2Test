method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test12() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 9.1130975 s
