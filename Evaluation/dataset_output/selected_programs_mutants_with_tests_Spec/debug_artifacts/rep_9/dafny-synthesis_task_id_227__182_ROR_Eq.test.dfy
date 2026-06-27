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

method {:test} Test24() {
var r0 := MinOfThree(14, 14, 14);
expect r0 <= 14 && r0 <= 14 && r0 <= 14;
expect r0 == 14 || r0 == 14 || r0 == 14;
}
method {:test} Test25() {
var r0 := MinOfThree(14, 13, 13);
expect r0 <= 14 && r0 <= 13 && r0 <= 13;
expect r0 == 14 || r0 == 13 || r0 == 13;
}
method {:test} Test26() {
var r0 := MinOfThree(14, 14, 13);
expect r0 <= 14 && r0 <= 14 && r0 <= 13;
expect r0 == 14 || r0 == 14 || r0 == 13;
}

// REPEAT 9 - TIME: 15.2093832 s
