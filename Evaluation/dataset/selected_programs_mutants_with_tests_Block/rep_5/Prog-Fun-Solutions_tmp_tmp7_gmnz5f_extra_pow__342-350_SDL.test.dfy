// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_pow.dfy

ghost function pow(a: int, e: nat): int
{
  if e == 0 then
    1
  else
    a * pow(a, e - 1)
}

method {:testEntry} Pow(a: nat, n: nat) returns (y: nat)
  ensures y == pow(a, n)
{
  var x: nat := 1;
  var k: nat := 0;
  while k < n
    invariant x == pow(a, k)
    invariant 0 <= k <= n
    decreases n - k
  {
    assert x == pow(a, k);
    assert x == a * pow(a, k);
    assert x == pow(a, k + 1);
    k := k + 1;
    assert x == pow(a, k);
  }
  assert k == n;
  y := x;
  assert y == pow(a, n);
}

method {:test} Test4() {
var r0 := Pow(5857, 1148);
}

// REPEAT 5 - TIME: 6.1440355 s
