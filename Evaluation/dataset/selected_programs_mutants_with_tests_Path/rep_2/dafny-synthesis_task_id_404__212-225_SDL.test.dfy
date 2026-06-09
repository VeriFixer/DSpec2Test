// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a <= b {
    minValue := a;
  } else {
  }
}

method {:test} Test2() {
var r0 := Min(2, 2);
expect r0 == 2 || r0 == 2;
expect r0 <= 2 && r0 <= 2;
}
method {:test} Test3() {
var r0 := Min(2, 1);
expect r0 == 2 || r0 == 1;
expect r0 <= 2 && r0 <= 1;
}

// REPEAT 2 - TIME: 2.3229114 s
