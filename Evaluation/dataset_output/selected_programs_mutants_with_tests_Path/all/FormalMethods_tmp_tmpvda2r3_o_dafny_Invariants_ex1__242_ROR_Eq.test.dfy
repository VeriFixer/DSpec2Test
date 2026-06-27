// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex1.dfy

method {:testEntry} Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m == 0
    invariant m * n + r == x * y
    invariant m >= 0
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

// REPEAT 1 - TIME: 5.4554319 s

method {:test} Test1() {
var r0 := Mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 9.3083736 s

method {:test} Test2() {
var r0 := Mult(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 12.2374039 s

method {:test} Test3() {
var r0 := Mult(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 15.019899 s

method {:test} Test4() {
var r0 := Mult(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 18.1749426 s

method {:test} Test5() {
var r0 := Mult(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 21.4909182 s

method {:test} Test6() {
var r0 := Mult(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 24.0617927 s

method {:test} Test7() {
var r0 := Mult(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 27.1811881 s

method {:test} Test8() {
var r0 := Mult(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 30.3950129 s

method {:test} Test9() {
var r0 := Mult(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 33.708005 s
