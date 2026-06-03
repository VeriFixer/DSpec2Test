// Clover_triple4.dfy

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := x;
}
