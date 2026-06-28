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

method {:test} Test27() {
var r0 := MinOfThree(15, 15, 15);
expect r0 <= 15 && r0 <= 15 && r0 <= 15;
expect r0 == 15 || r0 == 15 || r0 == 15;
}
method {:test} Test28() {
var r0 := MinOfThree(16, 15, 15);
expect r0 <= 16 && r0 <= 15 && r0 <= 15;
expect r0 == 16 || r0 == 15 || r0 == 15;
}
method {:test} Test29() {
var r0 := MinOfThree(16, 16, 15);
expect r0 <= 16 && r0 <= 16 && r0 <= 15;
expect r0 == 16 || r0 == 16 || r0 == 15;
}

// REPEAT 10 - TIME: 16.1499134 s
