// Metodos_Formais_tmp_tmpbez22nnn_Aula_2_ex2.dfy

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
  var b := x;
  var e := y;
  r := 1;
  while e <= 0
    invariant Potencia(b, e) * r == Potencia(x, y)
  {
    r := b * r;
    e := e - 1;
  }
  return r;
}
