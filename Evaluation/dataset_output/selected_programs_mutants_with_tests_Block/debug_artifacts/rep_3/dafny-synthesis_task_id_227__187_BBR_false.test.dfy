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

method {:test} Test7() {
var r0 := MinOfThree(5, 4, 3);
expect r0 <= 5 && r0 <= 4 && r0 <= 3;
expect r0 == 5 || r0 == 4 || r0 == 3;
}
method {:test} Test8() {
var r0 := MinOfThree(5, 4, 4);
expect r0 <= 5 && r0 <= 4 && r0 <= 4;
expect r0 == 5 || r0 == 4 || r0 == 4;
}
method {:test} Test9() {
var r0 := MinOfThree(4, 5, 3);
expect r0 <= 4 && r0 <= 5 && r0 <= 3;
expect r0 == 4 || r0 == 5 || r0 == 3;
}
method {:test} Test10() {
var r0 := MinOfThree(3, 4, 3);
expect r0 <= 3 && r0 <= 4 && r0 <= 3;
expect r0 == 3 || r0 == 4 || r0 == 3;
}

// REPEAT 3 - TIME: 8.3849207 s
