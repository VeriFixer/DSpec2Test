method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(108);
expect r0 == 108 * 108 * 108;
}

// REPEAT 9 - TIME: 11.0104722 s
