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

method {:test} Test40() {
var r0 := MinOfThree(16, 16, 16);
expect r0 <= 16 && r0 <= 16 && r0 <= 16;
expect r0 == 16 || r0 == 16 || r0 == 16;
}
method {:test} Test41() {
var r0 := MinOfThree(16, 16, 15);
expect r0 <= 16 && r0 <= 16 && r0 <= 15;
expect r0 == 16 || r0 == 16 || r0 == 15;
}
method {:test} Test42() {
var r0 := MinOfThree(16, 17, 15);
expect r0 <= 16 && r0 <= 17 && r0 <= 15;
expect r0 == 16 || r0 == 17 || r0 == 15;
}
method {:test} Test43() {
var r0 := MinOfThree(17, 16, 16);
expect r0 <= 17 && r0 <= 16 && r0 <= 16;
expect r0 == 17 || r0 == 16 || r0 == 16;
}
method {:test} Test44() {
var r0 := MinOfThree(17, 16, 15);
expect r0 <= 17 && r0 <= 16 && r0 <= 15;
expect r0 == 17 || r0 == 16 || r0 == 15;
}

// REPEAT 9 - TIME: 47.1726913 s
