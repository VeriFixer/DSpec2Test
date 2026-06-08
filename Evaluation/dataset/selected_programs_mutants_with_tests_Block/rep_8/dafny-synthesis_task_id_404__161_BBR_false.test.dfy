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

method {:test} Test14() {
var r0 := Min(11, 10);
expect r0 == 11 || r0 == 10;
expect r0 <= 11 && r0 <= 10;
}
method {:test} Test15() {
var r0 := Min(11, 11);
expect r0 == 11 || r0 == 11;
expect r0 <= 11 && r0 <= 11;
}

// REPEAT 8 - TIME: 10.5137189 s
