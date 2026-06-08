
method {:test} Test13() {
expect 6400240001.0/64000800.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(6400240001.0/64000800.0, 3.0, 6464240801.0/64000800.0);
expect r0 == 6464240801.0/64000800.0 - 1.0 / (4.0 * 6400240001.0/64000800.0);
}

// REPEAT 3 - TIME: 9.6618482 s