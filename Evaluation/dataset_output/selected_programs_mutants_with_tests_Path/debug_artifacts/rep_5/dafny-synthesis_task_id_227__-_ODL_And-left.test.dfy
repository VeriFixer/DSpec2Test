// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a <= c {
    min := a;
  } else if b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test20() {
var r0 := MinOfThree(8, 8, 8);
expect r0 <= 8 && r0 <= 8 && r0 <= 8;
expect r0 == 8 || r0 == 8 || r0 == 8;
}
method {:test} Test21() {
var r0 := MinOfThree(8, 8, 7);
expect r0 <= 8 && r0 <= 8 && r0 <= 7;
expect r0 == 8 || r0 == 8 || r0 == 7;
}
method {:test} Test22() {
var r0 := MinOfThree(8, 9, 7);
expect r0 <= 8 && r0 <= 9 && r0 <= 7;
expect r0 == 8 || r0 == 9 || r0 == 7;
}
method {:test} Test23() {
var r0 := MinOfThree(9, 8, 8);
expect r0 <= 9 && r0 <= 8 && r0 <= 8;
expect r0 == 9 || r0 == 8 || r0 == 8;
}
method {:test} Test24() {
var r0 := MinOfThree(9, 8, 7);
expect r0 <= 9 && r0 <= 8 && r0 <= 7;
expect r0 == 9 || r0 == 8 || r0 == 7;
}

// REPEAT 5 - TIME: 24.6908259 s
