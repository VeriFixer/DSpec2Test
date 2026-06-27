// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex1.dfy

method {:testEntry} Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m >= 0
    invariant m * n + r == x * y
    invariant m >= 0
  {
    r := r + n;
    m := m - 1;
  }
  return r;
}

method {:test} Test1() {
var r0 := Mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.6243081 s
