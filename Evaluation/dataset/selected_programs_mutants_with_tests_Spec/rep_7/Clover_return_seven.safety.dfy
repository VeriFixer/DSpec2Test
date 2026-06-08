method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test6() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 7.0638618 s
