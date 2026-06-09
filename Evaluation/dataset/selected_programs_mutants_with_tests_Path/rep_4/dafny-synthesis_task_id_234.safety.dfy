method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(4);
expect r0 == 4 * 4 * 4;
}

// REPEAT 4 - TIME: 6.1877817 s
