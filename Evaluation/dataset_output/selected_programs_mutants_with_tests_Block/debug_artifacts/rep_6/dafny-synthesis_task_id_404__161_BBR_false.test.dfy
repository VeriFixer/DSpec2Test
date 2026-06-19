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

method {:test} Test10() {
var r0 := Min(8, 7);
expect r0 == 8 || r0 == 7;
expect r0 <= 8 && r0 <= 7;
}
method {:test} Test11() {
var r0 := Min(8, 8);
expect r0 == 8 || r0 == 8;
expect r0 <= 8 && r0 <= 8;
}

// REPEAT 6 - TIME: 8.5572257 s
