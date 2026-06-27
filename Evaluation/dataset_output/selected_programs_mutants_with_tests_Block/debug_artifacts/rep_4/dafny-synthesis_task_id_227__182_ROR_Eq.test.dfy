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

method {:test} Test11() {
var r0 := MinOfThree(7, 6, 5);
expect r0 <= 7 && r0 <= 6 && r0 <= 5;
expect r0 == 7 || r0 == 6 || r0 == 5;
}
method {:test} Test12() {
var r0 := MinOfThree(6, 7, 5);
expect r0 <= 6 && r0 <= 7 && r0 <= 5;
expect r0 == 6 || r0 == 7 || r0 == 5;
}
method {:test} Test13() {
var r0 := MinOfThree(6, 6, 6);
expect r0 <= 6 && r0 <= 6 && r0 <= 6;
expect r0 == 6 || r0 == 6 || r0 == 6;
}

// REPEAT 4 - TIME: 9.2891622 s
