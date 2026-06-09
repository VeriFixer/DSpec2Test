method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    result := ((n << d) | (n >> (32 - d)));
}

method {:test} Test6() {
expect 0 <= 29 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 29);
expect r0 == ((1610612736 as bv32) << 29 as bv6) | ((1610612736 as bv32) >> (32 - 29) as bv6);
}

// REPEAT 7 - TIME: 8.1704605 s
