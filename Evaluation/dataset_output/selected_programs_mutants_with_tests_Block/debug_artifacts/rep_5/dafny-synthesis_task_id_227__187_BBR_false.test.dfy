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

method {:test} Test16() {
var r0 := MinOfThree(8, 9, 7);
expect r0 <= 8 && r0 <= 9 && r0 <= 7;
expect r0 == 8 || r0 == 9 || r0 == 7;
}
method {:test} Test17() {
var r0 := MinOfThree(9, 8, 8);
expect r0 <= 9 && r0 <= 8 && r0 <= 8;
expect r0 == 9 || r0 == 8 || r0 == 8;
}
method {:test} Test18() {
var r0 := MinOfThree(8, 9, 8);
expect r0 <= 8 && r0 <= 9 && r0 <= 8;
expect r0 == 8 || r0 == 9 || r0 == 8;
}

// REPEAT 5 - TIME: 11.8844413 s
