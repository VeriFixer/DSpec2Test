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

// REPEAT 1 - TIME: 9.6610886 s

method {:test} Test7() {
var r0 := Pot(101, 2440);
expect r0 == Potencia(101, 2440);
}

// REPEAT 2 - TIME: 10.8525712 s

method {:test} Test8() {
var r0 := Pot(102, 2441);
expect r0 == Potencia(102, 2441);
}

// REPEAT 3 - TIME: 11.7538861 s

method {:test} Test9() {
var r0 := Pot(103, 2442);
expect r0 == Potencia(103, 2442);
}

// REPEAT 4 - TIME: 12.7238763 s

method {:test} Test10() {
var r0 := Pot(104, 2443);
expect r0 == Potencia(104, 2443);
}

// REPEAT 5 - TIME: 13.5732357 s

method {:test} Test11() {
var r0 := Pot(105, 2444);
expect r0 == Potencia(105, 2444);
}

// REPEAT 6 - TIME: 14.587947 s

method {:test} Test12() {
var r0 := Pot(106, 2445);
expect r0 == Potencia(106, 2445);
}

// REPEAT 7 - TIME: 15.5689285 s

method {:test} Test13() {
var r0 := Pot(107, 2446);
expect r0 == Potencia(107, 2446);
}

// REPEAT 8 - TIME: 16.7457882 s

method {:test} Test14() {
var r0 := Pot(108, 2447);
expect r0 == Potencia(108, 2447);
}

// REPEAT 9 - TIME: 17.9317995 s

method {:test} Test15() {
var r0 := Pot(109, 2448);
expect r0 == Potencia(109, 2448);
}

// REPEAT 10 - TIME: 19.1231832 s
