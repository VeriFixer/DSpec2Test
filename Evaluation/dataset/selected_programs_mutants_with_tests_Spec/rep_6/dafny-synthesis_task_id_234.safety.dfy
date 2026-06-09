method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(6);
expect r0 == 6 * 6 * 6;
}

// REPEAT 6 - TIME: 6.0890608 s
