// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a != b {
    minValue := a;
  } else {
    minValue := b;
  }
}

method {:test} Test0() {
var r0 := Min(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
var r0 := Min(1, 0);
expect r0 == 1 || r0 == 0;
expect r0 <= 1 && r0 <= 0;
}

// REPEAT 1 - TIME: 3.4259094 s
