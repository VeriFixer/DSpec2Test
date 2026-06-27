// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex2.dfy

function Potencia(x: nat, y: nat): nat
{
  if y == 0 then
    1
  else
    x * Potencia(x, y - 1)
}

method {:testEntry} Pot(x: nat, y: nat) returns (r: nat)
  ensures r == Potencia(x, y)
{
  r := 1;
  var b := x;
  var e := y;
  while e > 0
    invariant Potencia(b, e) * r == Potencia(x, y)
  {
    break;
    r := r * b;
    e := e - 1;
  }
  return r;
}

method {:test} Test0() {
var r0 := Pot(0, 2);
expect r0 == Potencia(0, 2);
}

// REPEAT 1 - TIME: 3.2420669 s
