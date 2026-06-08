method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test8() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 7.2591009 s
