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

method {:test} Test45() {
var r0 := MinOfThree(18, 18, 18);
expect r0 <= 18 && r0 <= 18 && r0 <= 18;
expect r0 == 18 || r0 == 18 || r0 == 18;
}
method {:test} Test46() {
var r0 := MinOfThree(18, 18, 17);
expect r0 <= 18 && r0 <= 18 && r0 <= 17;
expect r0 == 18 || r0 == 18 || r0 == 17;
}
method {:test} Test47() {
var r0 := MinOfThree(18, 19, 17);
expect r0 <= 18 && r0 <= 19 && r0 <= 17;
expect r0 == 18 || r0 == 19 || r0 == 17;
}
method {:test} Test48() {
var r0 := MinOfThree(19, 18, 18);
expect r0 <= 19 && r0 <= 18 && r0 <= 18;
expect r0 == 19 || r0 == 18 || r0 == 18;
}
method {:test} Test49() {
var r0 := MinOfThree(19, 18, 17);
expect r0 <= 19 && r0 <= 18 && r0 <= 17;
expect r0 == 19 || r0 == 18 || r0 == 17;
}

// REPEAT 10 - TIME: 54.1943185 s
