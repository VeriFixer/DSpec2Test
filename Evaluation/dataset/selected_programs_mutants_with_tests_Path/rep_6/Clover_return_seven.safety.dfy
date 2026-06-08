method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test5() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 8.2361182 s
