// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x > 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
}

method {:test} Test0() {
var r0 := Triple(2573);
expect r0 == 3 * 2573;
}
method {:test} Test1() {
var r0 := Triple(-100);
expect r0 == 3 * -100;
}
method {:test} Test2() {
var r0 := Triple(100);
expect r0 == 3 * 100;
}
method {:test} Test3() {
var r0 := Triple(38);
expect r0 == 3 * 38;
}

// REPEAT 1 - TIME: 6.2677697 s
