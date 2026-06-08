method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(104);
expect r0 == 104 * 104 * 104;
}

// REPEAT 5 - TIME: 9.2018872 s
