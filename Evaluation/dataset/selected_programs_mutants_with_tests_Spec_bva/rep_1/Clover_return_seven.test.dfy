method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test0() {
var r0 := M(0);
expect r0 == 7;
}
method {:test} Test1() {
var r0 := M(-100);
expect r0 == 7;
}
method {:test} Test2() {
var r0 := M(100);
expect r0 == 7;
}

// REPEAT 1 - TIME: 4.9777219 s