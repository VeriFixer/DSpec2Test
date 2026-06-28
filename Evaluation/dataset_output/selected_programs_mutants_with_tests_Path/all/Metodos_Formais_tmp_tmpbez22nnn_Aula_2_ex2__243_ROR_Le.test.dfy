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


method {:test} Test0() {
var r0 := Pot(0, 2);
expect r0 == Potencia(0, 2);
}

// REPEAT 1 - TIME: 6.4811345 s

method {:test} Test1() {
var r0 := Pot(1, 3);
expect r0 == Potencia(1, 3);
}

// REPEAT 2 - TIME: 9.8961177 s

method {:test} Test2() {
var r0 := Pot(2, 4);
expect r0 == Potencia(2, 4);
}

// REPEAT 3 - TIME: 12.7395387 s

method {:test} Test3() {
var r0 := Pot(3, 5);
expect r0 == Potencia(3, 5);
}

// REPEAT 4 - TIME: 15.6033249 s

method {:test} Test4() {
var r0 := Pot(4, 6);
expect r0 == Potencia(4, 6);
}

// REPEAT 5 - TIME: 18.4487623 s

method {:test} Test5() {
var r0 := Pot(5, 7);
expect r0 == Potencia(5, 7);
}

// REPEAT 6 - TIME: 21.3289312 s

method {:test} Test6() {
var r0 := Pot(6, 8);
expect r0 == Potencia(6, 8);
}

// REPEAT 7 - TIME: 24.2054824 s

method {:test} Test7() {
var r0 := Pot(7, 9);
expect r0 == Potencia(7, 9);
}

// REPEAT 8 - TIME: 27.1334278 s

method {:test} Test8() {
var r0 := Pot(8, 10);
expect r0 == Potencia(8, 10);
}

// REPEAT 9 - TIME: 29.8996106 s

method {:test} Test9() {
var r0 := Pot(9, 11);
expect r0 == Potencia(9, 11);
}

// REPEAT 10 - TIME: 32.7679905 s
