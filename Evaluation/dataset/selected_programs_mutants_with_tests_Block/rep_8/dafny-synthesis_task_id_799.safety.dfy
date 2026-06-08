method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    result := ((n << d) | (n >> (32 - d)));
}

method {:test} Test7() {
expect 0 <= 7 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 7);
expect r0 == ((3758096384 as bv32) << 7 as bv6) | ((3758096384 as bv32) >> (32 - 7) as bv6);
}

// REPEAT 8 - TIME: 7.575226 s
