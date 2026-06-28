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

method {:test} Test30() {
var r0 := MinOfThree(16, 16, 15);
expect r0 <= 16 && r0 <= 16 && r0 <= 15;
expect r0 == 16 || r0 == 16 || r0 == 15;
}
method {:test} Test31() {
var r0 := MinOfThree(17, 16, 16);
expect r0 <= 17 && r0 <= 16 && r0 <= 16;
expect r0 == 17 || r0 == 16 || r0 == 16;
}
method {:test} Test32() {
var r0 := MinOfThree(16, 17, 15);
expect r0 <= 16 && r0 <= 17 && r0 <= 15;
expect r0 == 16 || r0 == 17 || r0 == 15;
}
method {:test} Test33() {
var r0 := MinOfThree(16, 17, 16);
expect r0 <= 16 && r0 <= 17 && r0 <= 16;
expect r0 == 16 || r0 == 17 || r0 == 16;
}

// REPEAT 9 - TIME: 18.593266 s
