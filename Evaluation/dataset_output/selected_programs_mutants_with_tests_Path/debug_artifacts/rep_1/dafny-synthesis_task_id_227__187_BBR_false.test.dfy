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

method {:test} Test0() {
var r0 := MinOfThree(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0 || r0 == 0;
}
method {:test} Test1() {
var r0 := MinOfThree(0, 0, -1);
expect r0 <= 0 && r0 <= 0 && r0 <= -1;
expect r0 == 0 || r0 == 0 || r0 == -1;
}
method {:test} Test2() {
var r0 := MinOfThree(0, 1, -1);
expect r0 <= 0 && r0 <= 1 && r0 <= -1;
expect r0 == 0 || r0 == 1 || r0 == -1;
}
method {:test} Test3() {
var r0 := MinOfThree(1, 0, 0);
expect r0 <= 1 && r0 <= 0 && r0 <= 0;
expect r0 == 1 || r0 == 0 || r0 == 0;
}
method {:test} Test4() {
var r0 := MinOfThree(1, 0, -1);
expect r0 <= 1 && r0 <= 0 && r0 <= -1;
expect r0 == 1 || r0 == 0 || r0 == -1;
}

// REPEAT 1 - TIME: 6.8712224 s
