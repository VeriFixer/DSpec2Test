method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(8);
expect r0 == 8 * 8 * 8;
}

// REPEAT 8 - TIME: 9.2654098 s
