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

method {:test} Test35() {
var r0 := MinOfThree(14, 14, 14);
expect r0 <= 14 && r0 <= 14 && r0 <= 14;
expect r0 == 14 || r0 == 14 || r0 == 14;
}
method {:test} Test36() {
var r0 := MinOfThree(14, 14, 13);
expect r0 <= 14 && r0 <= 14 && r0 <= 13;
expect r0 == 14 || r0 == 14 || r0 == 13;
}
method {:test} Test37() {
var r0 := MinOfThree(14, 15, 13);
expect r0 <= 14 && r0 <= 15 && r0 <= 13;
expect r0 == 14 || r0 == 15 || r0 == 13;
}
method {:test} Test38() {
var r0 := MinOfThree(15, 14, 14);
expect r0 <= 15 && r0 <= 14 && r0 <= 14;
expect r0 == 15 || r0 == 14 || r0 == 14;
}
method {:test} Test39() {
var r0 := MinOfThree(15, 14, 13);
expect r0 <= 15 && r0 <= 14 && r0 <= 13;
expect r0 == 15 || r0 == 14 || r0 == 13;
}

// REPEAT 8 - TIME: 39.9184284 s
