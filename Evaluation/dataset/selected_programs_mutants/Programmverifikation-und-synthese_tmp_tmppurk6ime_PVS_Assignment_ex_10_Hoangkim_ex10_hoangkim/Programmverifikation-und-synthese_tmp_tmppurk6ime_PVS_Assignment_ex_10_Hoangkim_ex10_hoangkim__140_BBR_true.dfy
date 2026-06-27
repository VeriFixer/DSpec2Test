// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_10_Hoangkim_ex10_hoangkim.dfy

method {:testEntry} square0(n: nat) returns (sqn: nat)
  ensures sqn == n * n
{
  sqn := 0;
  var i := 0;
  var x;
  while true
    invariant i <= n && sqn == i * i
  {
    x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
}

method {:testEntry} square1(n: nat) returns (sqn: nat)
  ensures sqn == n * n
{
  sqn := 0;
  var i := 0;
  while i < n
    invariant i <= n && sqn == i * i
  {
    var x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
}

method {:testEntry} q(x: nat, y: nat) returns (z: nat)
  requires y - x > 2
  ensures x < z * z < y

method {:testEntry} strange()
  ensures 1 == 2
{
  var x := 4;
  var c: nat := q(x, 2 * x);
}

method {:testEntry} test0()
{
  var x: int := *;
  assume x * x < 100;
  assert x <= 9;
}
