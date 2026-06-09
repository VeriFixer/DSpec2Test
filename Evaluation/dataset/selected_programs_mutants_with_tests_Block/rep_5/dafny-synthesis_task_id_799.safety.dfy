method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    result := ((n << d) | (n >> (32 - d)));
}

method {:test} Test4() {
expect 0 <= 4 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((536870912 as bv32), 4);
expect r0 == ((536870912 as bv32) << 4 as bv6) | ((536870912 as bv32) >> (32 - 4) as bv6);
}

// REPEAT 5 - TIME: 5.0405301 s
