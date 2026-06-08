method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    result := ((n << d) | (n >> (32 - d)));
}

method {:test} Test2() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 2);
expect r0 == ((1073741824 as bv32) << 2 as bv6) | ((1073741824 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 3 - TIME: 5.8723655 s
