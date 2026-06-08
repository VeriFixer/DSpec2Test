// Clover_return_seven.dfy

method {:testEntry} M(x: int) returns (seven: int)
  ensures seven == 7
{
  seven := 6;
}

method {:test} Test0() {
var r0 := M(0);
expect r0 == 7;
}

// REPEAT 1 - TIME: 2.710037 s
