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

method {:test} Test15() {
var r0 := MinOfThree(9, 9, 9);
expect r0 <= 9 && r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9 || r0 == 9;
}
method {:test} Test16() {
var r0 := MinOfThree(9, 8, 8);
expect r0 <= 9 && r0 <= 8 && r0 <= 8;
expect r0 == 9 || r0 == 8 || r0 == 8;
}
method {:test} Test17() {
var r0 := MinOfThree(9, 9, 8);
expect r0 <= 9 && r0 <= 9 && r0 <= 8;
expect r0 == 9 || r0 == 9 || r0 == 8;
}

// REPEAT 6 - TIME: 10.611729 s
