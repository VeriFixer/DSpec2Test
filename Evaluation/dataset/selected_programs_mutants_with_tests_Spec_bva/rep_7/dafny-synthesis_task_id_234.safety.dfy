method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(106);
expect r0 == 106 * 106 * 106;
}

// REPEAT 7 - TIME: 9.535317 s
