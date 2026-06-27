// FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex1.dfy

method {:testEntry} Mult(x: nat, y: nat) returns (r: nat)
  ensures r == x * y
{
  var m := x;
  var n := y;
  r := 0;
  while m <= 0
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

// REPEAT 1 - TIME: 2.3154864 s
