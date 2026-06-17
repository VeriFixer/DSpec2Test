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

method {:test} Test18() {
var r0 := Min(14, 14);
expect r0 == 14 || r0 == 14;
expect r0 <= 14 && r0 <= 14;
}
method {:test} Test19() {
var r0 := Min(14, 13);
expect r0 == 14 || r0 == 13;
expect r0 <= 14 && r0 <= 13;
}

// REPEAT 10 - TIME: 12.1161992 s
