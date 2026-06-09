method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    result := ((n << d) | (n >> (32 - d)));
}

method {:test} Test8() {
expect 0 <= 8 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((268435456 as bv32), 8);
expect r0 == ((268435456 as bv32) << 8 as bv6) | ((268435456 as bv32) >> (32 - 8) as bv6);
}

// REPEAT 9 - TIME: 6.2978992 s
