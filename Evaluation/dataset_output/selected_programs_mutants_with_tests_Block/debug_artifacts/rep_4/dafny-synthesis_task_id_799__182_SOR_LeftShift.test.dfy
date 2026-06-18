// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := (n << d) | (n << (32 - d));
}

method {:test} Test3() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 2);
expect r0 == ((3221225472 as bv32) << 2 as bv6) | ((3221225472 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 4 - TIME: 4.60006 s
