// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method {:testEntry} TripleConditions(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3 * x
{
  r := 6;
  assert r == 3 * x;
}
