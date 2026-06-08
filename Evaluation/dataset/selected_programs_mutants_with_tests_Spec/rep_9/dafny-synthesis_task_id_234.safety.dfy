method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(9);
expect r0 == 9 * 9 * 9;
}

// REPEAT 9 - TIME: 9.5253131 s
