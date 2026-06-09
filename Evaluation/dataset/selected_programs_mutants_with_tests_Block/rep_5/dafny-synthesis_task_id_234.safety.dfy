method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(5);
expect r0 == 5 * 5 * 5;
}

// REPEAT 5 - TIME: 4.7822595 s
