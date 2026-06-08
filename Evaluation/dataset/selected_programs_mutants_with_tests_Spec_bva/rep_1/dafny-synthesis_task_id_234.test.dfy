method {:testEntry} CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(1);
expect r0 == 1 * 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(100);
expect r0 == 100 * 100 * 100;
}

// REPEAT 1 - TIME: 6.153593 s