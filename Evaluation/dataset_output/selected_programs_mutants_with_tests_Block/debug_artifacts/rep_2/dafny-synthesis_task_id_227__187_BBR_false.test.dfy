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

method {:test} Test4() {
var r0 := MinOfThree(2, 3, 1);
expect r0 <= 2 && r0 <= 3 && r0 <= 1;
expect r0 == 2 || r0 == 3 || r0 == 1;
}
method {:test} Test5() {
var r0 := MinOfThree(2, 1, 1);
expect r0 <= 2 && r0 <= 1 && r0 <= 1;
expect r0 == 2 || r0 == 1 || r0 == 1;
}
method {:test} Test6() {
var r0 := MinOfThree(2, 3, 2);
expect r0 <= 2 && r0 <= 3 && r0 <= 2;
expect r0 == 2 || r0 == 3 || r0 == 2;
}

// REPEAT 2 - TIME: 5.5297896 s
