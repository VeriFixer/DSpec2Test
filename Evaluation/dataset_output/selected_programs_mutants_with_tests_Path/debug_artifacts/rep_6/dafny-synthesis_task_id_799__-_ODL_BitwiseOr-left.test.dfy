// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := n >> (32 - d);
}

method {:test} Test5() {
expect 0 <= 6 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 6);
expect r0 == ((2684354560 as bv32) << 6 as bv6) | ((2684354560 as bv32) >> (32 - 6) as bv6);
}

// REPEAT 6 - TIME: 4.5744878 s
