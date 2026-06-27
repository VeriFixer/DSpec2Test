// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method {:testEntry} Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i > n
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
}

method {:test} Test0() {
var r0 := Cube(0);
expect r0 == 0 * 0 * 0;
}
method {:test} Test1() {
var r0 := Cube(100);
expect r0 == 100 * 100 * 100;
}

// REPEAT 1 - TIME: 6.2046754 s
