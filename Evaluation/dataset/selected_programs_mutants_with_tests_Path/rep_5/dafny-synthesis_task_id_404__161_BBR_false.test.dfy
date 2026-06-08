// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if false {
    minValue := a;
  } else {
    minValue := b;
  }
}

method {:test} Test8() {
var r0 := Min(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 <= 6 && r0 <= 6;
}
method {:test} Test9() {
var r0 := Min(7, 6);
expect r0 == 7 || r0 == 6;
expect r0 <= 7 && r0 <= 6;
}

// REPEAT 5 - TIME: 10.1039893 s
