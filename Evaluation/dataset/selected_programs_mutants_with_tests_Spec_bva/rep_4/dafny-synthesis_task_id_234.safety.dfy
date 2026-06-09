method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(103);
expect r0 == 103 * 103 * 103;
}

// REPEAT 4 - TIME: 7.4718579 s
