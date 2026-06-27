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

method {:test} Test6() {
var r0 := MinOfThree(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4 || r0 == 4;
}
method {:test} Test7() {
var r0 := MinOfThree(4, 3, 3);
expect r0 <= 4 && r0 <= 3 && r0 <= 3;
expect r0 == 4 || r0 == 3 || r0 == 3;
}
method {:test} Test8() {
var r0 := MinOfThree(4, 4, 3);
expect r0 <= 4 && r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 4 || r0 == 3;
}

// REPEAT 3 - TIME: 7.0718126 s
