// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := (n << d) & (n >> (32 - d));
}

method {:test} Test10() {
expect 0 <= 30 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2147483648 as bv32), 30);
expect r0 == ((2147483648 as bv32) << 30 as bv6) | ((2147483648 as bv32) >> (32 - 30) as bv6);
}

// REPEAT 2 - TIME: 7.2723502 s
