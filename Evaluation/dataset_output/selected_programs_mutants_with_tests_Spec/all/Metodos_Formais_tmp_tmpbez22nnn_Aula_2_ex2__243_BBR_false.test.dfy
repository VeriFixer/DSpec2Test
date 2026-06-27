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
  while false
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

// REPEAT 1 - TIME: 3.3407579 s

method {:test} Test1() {
var r0 := Pot(1, 3);
expect r0 == Potencia(1, 3);
}

// REPEAT 2 - TIME: 4.3925664 s

method {:test} Test2() {
var r0 := Pot(2, 4);
expect r0 == Potencia(2, 4);
}

// REPEAT 3 - TIME: 5.4816483 s

method {:test} Test3() {
var r0 := Pot(3, 5);
expect r0 == Potencia(3, 5);
}

// REPEAT 4 - TIME: 6.570712 s

method {:test} Test4() {
var r0 := Pot(4, 6);
expect r0 == Potencia(4, 6);
}

// REPEAT 5 - TIME: 7.5617065 s

method {:test} Test5() {
var r0 := Pot(5, 7);
expect r0 == Potencia(5, 7);
}

// REPEAT 6 - TIME: 8.4612863 s

method {:test} Test6() {
var r0 := Pot(6, 8);
expect r0 == Potencia(6, 8);
}

// REPEAT 7 - TIME: 9.5306064 s

method {:test} Test7() {
var r0 := Pot(7, 9);
expect r0 == Potencia(7, 9);
}

// REPEAT 8 - TIME: 10.343571 s

method {:test} Test8() {
var r0 := Pot(8, 10);
expect r0 == Potencia(8, 10);
}

// REPEAT 9 - TIME: 11.0398992 s

method {:test} Test9() {
var r0 := Pot(9, 11);
expect r0 == Potencia(9, 11);
}

// REPEAT 10 - TIME: 11.9630466 s
