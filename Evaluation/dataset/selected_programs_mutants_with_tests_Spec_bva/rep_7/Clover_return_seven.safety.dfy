method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test11() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 9.1326084 s
