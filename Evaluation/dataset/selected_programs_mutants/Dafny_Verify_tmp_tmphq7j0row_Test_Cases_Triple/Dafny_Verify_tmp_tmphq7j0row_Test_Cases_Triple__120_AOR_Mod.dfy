// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method {:testEntry} TripleConditions(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3 * x
{
  var y := x % 2;
  r := 6 * y;
  assert r == 3 * x;
}
