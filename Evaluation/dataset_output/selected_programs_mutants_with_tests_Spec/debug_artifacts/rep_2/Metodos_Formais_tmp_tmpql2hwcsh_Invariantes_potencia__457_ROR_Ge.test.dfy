// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_potencia.dfy

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
  while e >= 0
    invariant Potencia(b, e) * r == Potencia(x, y)
  {
    r := r * b;
    e := e - 1;
  }
  return r;
}

method {:test} Test1() {
var r0 := Pot(1, 3);
expect r0 == Potencia(1, 3);
}

// REPEAT 2 - TIME: 3.9414416 s
