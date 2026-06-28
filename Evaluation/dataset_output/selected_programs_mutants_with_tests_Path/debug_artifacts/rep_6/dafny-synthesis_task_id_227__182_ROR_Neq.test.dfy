// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a != b && a <= c {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test25() {
var r0 := MinOfThree(10, 10, 10);
expect r0 <= 10 && r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10 || r0 == 10;
}
method {:test} Test26() {
var r0 := MinOfThree(10, 10, 9);
expect r0 <= 10 && r0 <= 10 && r0 <= 9;
expect r0 == 10 || r0 == 10 || r0 == 9;
}
method {:test} Test27() {
var r0 := MinOfThree(10, 11, 9);
expect r0 <= 10 && r0 <= 11 && r0 <= 9;
expect r0 == 10 || r0 == 11 || r0 == 9;
}
method {:test} Test28() {
var r0 := MinOfThree(11, 10, 10);
expect r0 <= 11 && r0 <= 10 && r0 <= 10;
expect r0 == 11 || r0 == 10 || r0 == 10;
}
method {:test} Test29() {
var r0 := MinOfThree(11, 10, 9);
expect r0 <= 11 && r0 <= 10 && r0 <= 9;
expect r0 == 11 || r0 == 10 || r0 == 9;
}

// REPEAT 6 - TIME: 29.4499403 s
