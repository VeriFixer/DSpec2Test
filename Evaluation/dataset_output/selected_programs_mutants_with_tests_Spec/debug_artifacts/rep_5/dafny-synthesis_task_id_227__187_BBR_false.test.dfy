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

method {:test} Test12() {
var r0 := MinOfThree(7, 7, 7);
expect r0 <= 7 && r0 <= 7 && r0 <= 7;
expect r0 == 7 || r0 == 7 || r0 == 7;
}
method {:test} Test13() {
var r0 := MinOfThree(8, 7, 7);
expect r0 <= 8 && r0 <= 7 && r0 <= 7;
expect r0 == 8 || r0 == 7 || r0 == 7;
}
method {:test} Test14() {
var r0 := MinOfThree(7, 7, 6);
expect r0 <= 7 && r0 <= 7 && r0 <= 6;
expect r0 == 7 || r0 == 7 || r0 == 6;
}

// REPEAT 5 - TIME: 10.4142506 s
