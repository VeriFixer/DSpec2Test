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

method {:test} Test18() {
var r0 := MinOfThree(10, 10, 10);
expect r0 <= 10 && r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10 || r0 == 10;
}
method {:test} Test19() {
var r0 := MinOfThree(11, 10, 10);
expect r0 <= 11 && r0 <= 10 && r0 <= 10;
expect r0 == 11 || r0 == 10 || r0 == 10;
}
method {:test} Test20() {
var r0 := MinOfThree(11, 11, 10);
expect r0 <= 11 && r0 <= 11 && r0 <= 10;
expect r0 == 11 || r0 == 11 || r0 == 10;
}

// REPEAT 7 - TIME: 12.095231 s
