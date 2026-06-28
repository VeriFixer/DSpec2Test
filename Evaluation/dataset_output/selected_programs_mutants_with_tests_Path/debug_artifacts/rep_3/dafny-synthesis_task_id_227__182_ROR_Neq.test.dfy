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

method {:test} Test10() {
var r0 := MinOfThree(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4 || r0 == 4;
}
method {:test} Test11() {
var r0 := MinOfThree(4, 4, 3);
expect r0 <= 4 && r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 4 || r0 == 3;
}
method {:test} Test12() {
var r0 := MinOfThree(4, 5, 3);
expect r0 <= 4 && r0 <= 5 && r0 <= 3;
expect r0 == 4 || r0 == 5 || r0 == 3;
}
method {:test} Test13() {
var r0 := MinOfThree(5, 4, 4);
expect r0 <= 5 && r0 <= 4 && r0 <= 4;
expect r0 == 5 || r0 == 4 || r0 == 4;
}
method {:test} Test14() {
var r0 := MinOfThree(5, 4, 3);
expect r0 <= 5 && r0 <= 4 && r0 <= 3;
expect r0 == 5 || r0 == 4 || r0 == 3;
}

// REPEAT 3 - TIME: 14.6325257 s
