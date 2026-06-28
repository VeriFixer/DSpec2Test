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

method {:test} Test3() {
var r0 := MinOfThree(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
expect r0 == 2 || r0 == 2 || r0 == 2;
}
method {:test} Test4() {
var r0 := MinOfThree(3, 2, 2);
expect r0 <= 3 && r0 <= 2 && r0 <= 2;
expect r0 == 3 || r0 == 2 || r0 == 2;
}
method {:test} Test5() {
var r0 := MinOfThree(2, 2, 1);
expect r0 <= 2 && r0 <= 2 && r0 <= 1;
expect r0 == 2 || r0 == 2 || r0 == 1;
}

// REPEAT 2 - TIME: 5.401624 s
