method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(3);
expect r0 == 3 * 3 * 3;
}

// REPEAT 3 - TIME: 5.1792307 s
