// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy

method {:testEntry} Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x;
  while x > 0
    invariant x >= 0
    invariant z == x * y
    decreases x
  {
    x := x - 1;
    z := z - y;
  }
}

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(1, 1);
expect r0 == 0;
}

// REPEAT 2 - TIME: 9.680549 s
