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

method {:test} Test23() {
var r0 := MinOfThree(13, 12, 11);
expect r0 <= 13 && r0 <= 12 && r0 <= 11;
expect r0 == 13 || r0 == 12 || r0 == 11;
}
method {:test} Test24() {
var r0 := MinOfThree(12, 13, 11);
expect r0 <= 12 && r0 <= 13 && r0 <= 11;
expect r0 == 12 || r0 == 13 || r0 == 11;
}
method {:test} Test25() {
var r0 := MinOfThree(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12 || r0 == 12;
}

// REPEAT 7 - TIME: 14.9072461 s
