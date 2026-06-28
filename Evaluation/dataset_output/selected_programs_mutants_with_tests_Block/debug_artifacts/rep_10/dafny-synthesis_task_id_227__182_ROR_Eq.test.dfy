// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a == b && a <= c {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test34() {
var r0 := MinOfThree(19, 18, 17);
expect r0 <= 19 && r0 <= 18 && r0 <= 17;
expect r0 == 19 || r0 == 18 || r0 == 17;
}
method {:test} Test35() {
var r0 := MinOfThree(18, 19, 17);
expect r0 <= 18 && r0 <= 19 && r0 <= 17;
expect r0 == 18 || r0 == 19 || r0 == 17;
}
method {:test} Test36() {
var r0 := MinOfThree(18, 18, 18);
expect r0 <= 18 && r0 <= 18 && r0 <= 18;
expect r0 == 18 || r0 == 18 || r0 == 18;
}

// REPEAT 10 - TIME: 19.8201035 s
