method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(105);
expect r0 == 105 * 105 * 105;
}

// REPEAT 6 - TIME: 9.7908852 s
