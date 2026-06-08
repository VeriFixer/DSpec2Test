method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(109);
expect r0 == 109 * 109 * 109;
}

// REPEAT 10 - TIME: 12.4409137 s
