// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if false {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test18() {
var r0 := MinOfThree(11, 10, 9);
expect r0 <= 11 && r0 <= 10 && r0 <= 9;
expect r0 == 11 || r0 == 10 || r0 == 9;
}
method {:test} Test19() {
var r0 := MinOfThree(11, 10, 10);
expect r0 <= 11 && r0 <= 10 && r0 <= 10;
expect r0 == 11 || r0 == 10 || r0 == 10;
}
method {:test} Test20() {
var r0 := MinOfThree(10, 11, 9);
expect r0 <= 10 && r0 <= 11 && r0 <= 9;
expect r0 == 10 || r0 == 11 || r0 == 9;
}
method {:test} Test21() {
var r0 := MinOfThree(10, 11, 10);
expect r0 <= 10 && r0 <= 11 && r0 <= 10;
expect r0 == 10 || r0 == 11 || r0 == 10;
}

// REPEAT 6 - TIME: 13.1398316 s
