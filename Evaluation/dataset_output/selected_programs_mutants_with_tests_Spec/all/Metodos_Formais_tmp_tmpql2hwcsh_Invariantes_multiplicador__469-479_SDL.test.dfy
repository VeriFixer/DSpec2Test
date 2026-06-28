// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_multiplicador.dfy

method {:testEntry} Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m > 0
    invariant m >= 0
    invariant m * n + r == x * y
  {
    m := m - 1;
  }
  return r;
}


method {:test} Test0() {
var r0 := Mult(0, 0);
expect r0 == 0 * 0;
}

// REPEAT 1 - TIME: 2.8865952 s

method {:test} Test1() {
var r0 := Mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 4.040504 s

method {:test} Test2() {
var r0 := Mult(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 5.1005195 s

method {:test} Test3() {
var r0 := Mult(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 6.1924245 s

method {:test} Test4() {
var r0 := Mult(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 7.3832198 s

method {:test} Test5() {
var r0 := Mult(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 8.3524449 s

method {:test} Test6() {
var r0 := Mult(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 9.2698403 s

method {:test} Test7() {
var r0 := Mult(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 10.0964788 s

method {:test} Test8() {
var r0 := Mult(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 10.8156662 s

method {:test} Test9() {
var r0 := Mult(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 11.5759563 s
