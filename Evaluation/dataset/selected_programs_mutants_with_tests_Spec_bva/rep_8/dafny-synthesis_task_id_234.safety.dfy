method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(107);
expect r0 == 107 * 107 * 107;
}

// REPEAT 8 - TIME: 11.1070282 s
