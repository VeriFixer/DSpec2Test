// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := n >> (32 - d);
}

method {:test} Test9() {
expect 0 <= 12 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2415919104 as bv32), 12);
expect r0 == ((2415919104 as bv32) << 12 as bv6) | ((2415919104 as bv32) >> (32 - 12) as bv6);
}

// REPEAT 10 - TIME: 8.7290118 s
