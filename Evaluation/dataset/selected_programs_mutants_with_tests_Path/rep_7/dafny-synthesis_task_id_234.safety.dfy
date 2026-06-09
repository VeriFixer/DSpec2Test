method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(7);
expect r0 == 7 * 7 * 7;
}

// REPEAT 7 - TIME: 9.3426114 s
