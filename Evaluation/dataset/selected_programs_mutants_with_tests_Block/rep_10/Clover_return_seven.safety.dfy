method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test9() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 7.847754 s
