// Metodos_Formais_tmp_tmpbez22nnn_Aula_2_ex1.dfy

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
    break;
    r := r + n;
    m := m - 1;
  }
  return r;
}

method {:test} Test0() {
var r0 := Mult(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test1() {
var r0 := Mult(100, 38);
expect r0 == 100 * 38;
}
method {:test} Test2() {
var r0 := Mult(38, 100);
expect r0 == 38 * 100;
}
method {:test} Test4() {
var r0 := Mult(1, 100);
expect r0 == 1 * 100;
}

// REPEAT 1 - TIME: 6.1450016 s
