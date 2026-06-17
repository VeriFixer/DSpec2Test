// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a == b {
    minValue := a;
  } else {
    minValue := b;
  }
}

method {:test} Test6() {
var r0 := Min(5, 4);
expect r0 == 5 || r0 == 4;
expect r0 <= 5 && r0 <= 4;
}
method {:test} Test7() {
var r0 := Min(5, 5);
expect r0 == 5 || r0 == 5;
expect r0 <= 5 && r0 <= 5;
}

// REPEAT 4 - TIME: 5.9530659 s
