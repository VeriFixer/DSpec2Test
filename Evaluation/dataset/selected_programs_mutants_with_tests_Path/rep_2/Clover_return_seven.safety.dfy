method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test1() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 3.5188992 s
