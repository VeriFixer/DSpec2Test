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

method {:test} Test26() {
var r0 := MinOfThree(15, 14, 13);
expect r0 <= 15 && r0 <= 14 && r0 <= 13;
expect r0 == 15 || r0 == 14 || r0 == 13;
}
method {:test} Test27() {
var r0 := MinOfThree(15, 14, 14);
expect r0 <= 15 && r0 <= 14 && r0 <= 14;
expect r0 == 15 || r0 == 14 || r0 == 14;
}
method {:test} Test28() {
var r0 := MinOfThree(14, 15, 13);
expect r0 <= 14 && r0 <= 15 && r0 <= 13;
expect r0 == 14 || r0 == 15 || r0 == 13;
}
method {:test} Test29() {
var r0 := MinOfThree(14, 15, 14);
expect r0 <= 14 && r0 <= 15 && r0 <= 14;
expect r0 == 14 || r0 == 15 || r0 == 14;
}

// REPEAT 8 - TIME: 16.2804462 s
