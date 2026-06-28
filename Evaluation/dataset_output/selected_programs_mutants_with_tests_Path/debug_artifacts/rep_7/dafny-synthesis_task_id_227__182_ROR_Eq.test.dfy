// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a == b && a <= c {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test30() {
var r0 := MinOfThree(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12 || r0 == 12;
}
method {:test} Test31() {
var r0 := MinOfThree(12, 12, 11);
expect r0 <= 12 && r0 <= 12 && r0 <= 11;
expect r0 == 12 || r0 == 12 || r0 == 11;
}
method {:test} Test32() {
var r0 := MinOfThree(12, 13, 11);
expect r0 <= 12 && r0 <= 13 && r0 <= 11;
expect r0 == 12 || r0 == 13 || r0 == 11;
}
method {:test} Test33() {
var r0 := MinOfThree(13, 12, 12);
expect r0 <= 13 && r0 <= 12 && r0 <= 12;
expect r0 == 13 || r0 == 12 || r0 == 12;
}
method {:test} Test34() {
var r0 := MinOfThree(13, 12, 11);
expect r0 <= 13 && r0 <= 12 && r0 <= 11;
expect r0 == 13 || r0 == 12 || r0 == 11;
}

// REPEAT 7 - TIME: 34.4800656 s
