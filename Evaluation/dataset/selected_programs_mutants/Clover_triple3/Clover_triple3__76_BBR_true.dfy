// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if true {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
}
