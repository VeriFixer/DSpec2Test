
method {:test} Test7() {
var r0 := CountEqualNumbers(33, 32, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 32 && 32 == 32;
expect r0 == 2 <==> (33 == 32 && 32 != 32) || (33 != 32 && 32 == 32) || (33 == 32 && 32 != 32);
expect r0 == 1 <==> 33 != 32 && 32 != 32 && 33 != 32;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}

// REPEAT 4 - TIME: 6.8412347 s