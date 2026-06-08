method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(102);
expect r0 == 102 * 102 * 102;
}

// REPEAT 3 - TIME: 7.9124111 s
