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

method {:test} Test21() {
var r0 := MinOfThree(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12 || r0 == 12;
}
method {:test} Test22() {
var r0 := MinOfThree(13, 12, 12);
expect r0 <= 13 && r0 <= 12 && r0 <= 12;
expect r0 == 13 || r0 == 12 || r0 == 12;
}
method {:test} Test23() {
var r0 := MinOfThree(12, 12, 11);
expect r0 <= 12 && r0 <= 12 && r0 <= 11;
expect r0 == 12 || r0 == 12 || r0 == 11;
}

// REPEAT 8 - TIME: 13.5181404 s
