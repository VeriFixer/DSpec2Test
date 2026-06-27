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
  while e > 0
    invariant Potencia(b, e) * r == Potencia(x, y)
  {
    break;
    r := b * r;
    e := e - 1;
  }
  return r;
}

method {:test} Test0() {
var r0 := Pot(0, 2);
expect r0 == Potencia(0, 2);
}
method {:test} Test1() {
var r0 := Pot(100, 2439);
expect r0 == Potencia(100, 2439);
}
method {:test} Test2() {
var r0 := Pot(0, 100);
expect r0 == Potencia(0, 100);
}
method {:test} Test4() {
var r0 := Pot(1, 592);
expect r0 == Potencia(1, 592);
}

// REPEAT 1 - TIME: 7.6306733 s
