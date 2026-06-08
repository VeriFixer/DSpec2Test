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
