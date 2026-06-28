// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_multiplicador.dfy

method {:testEntry} Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m >= 0
    invariant m >= 0
    invariant m * n + r == x * y
  {
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

// REPEAT 1 - TIME: 9.2661429 s

method {:test} Test7() {
var r0 := Mult(101, 101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 10.176767 s

method {:test} Test8() {
var r0 := Mult(102, 102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 11.0902667 s

method {:test} Test9() {
var r0 := Mult(103, 103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 12.1047724 s

method {:test} Test10() {
var r0 := Mult(104, 104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 13.3154605 s

method {:test} Test11() {
var r0 := Mult(105, 105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 14.3225049 s

method {:test} Test12() {
var r0 := Mult(106, 106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 15.2388458 s

method {:test} Test13() {
var r0 := Mult(107, 107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 16.0332109 s

method {:test} Test14() {
var r0 := Mult(108, 108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 16.9743886 s

method {:test} Test15() {
var r0 := Mult(109, 109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 17.8179997 s
