// MFS_tmp_tmpmmnu354t_Praticas_TP9_Power.dfy

function power(x: real, n: nat): real
{
  if n == 0 then
    1.0
  else
    x * power(x, n - 1)
}

method powerIter(b: real, n: nat) returns (p: real)
  ensures p == power(b, n)
{
  p := 1.0;
  var i := 0;
  while i != n
    invariant p == power(b, i) && 0 <= i <= n
  {
    p := p * b;
    i := i + 1;
  }
}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
  ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
{
}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
  ensures power(x, a) * power(x, b) == power(x, a + b)
{
  if a == 0 {
    assert power(x, a) * power(x, b) == 1.0 * power(x, b) == power(x, b) == power(x, a + b);
  } else {
    distributiveProperty(x, a - 1, b);
    assert power(x, a) * power(x, b) == x * power(x, a - 1) * power(x, b) == x * (power(x, a - 1) * power(x, b)) == x * power(x, a - 1 + b) == power(x, a + b);
  }
}

method powerOpt(b: real, n: nat) returns (p: real)
  ensures p == power(b, n)
{
  if n == 0 {
    return 1.0;
  } else if n % 2 == 0 {
    distributiveProperty(b, n / 2, n / 2);
    var r := powerOpt(b, n / 2);
    return r * r;
  } else {
    distributiveProperty(b, (n - 1) / 2, (n - 1) / 2);
    var r := powerOpt(b, (n - 1) / 2);
    return r * r * b;
  }
}

method testPower()
{
  var p1 := powerIter(2.0, 5);
  var p2 := powerOpt(2.0, 5);
  print "P1: ", p1, "\n";
  print "P2: ", p2, "\n";
  assert p1 == 32.0;
  assert p2 == 32.0;
}
