
method {:test} Test3() {
var r0 := CountEqualNumbers(28, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 27;
expect r0 == 2 <==> (28 == 27 && 27 != 27) || (28 != 27 && 27 == 27) || (28 == 27 && 27 != 27);
expect r0 == 1 <==> 28 != 27 && 27 != 27 && 28 != 27;
}
method {:test} Test4() {
var r0 := CountEqualNumbers(27, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 27 == 27 && 27 == 27;
expect r0 == 2 <==> (27 == 27 && 27 != 27) || (27 != 27 && 27 == 27) || (27 == 27 && 27 != 27);
expect r0 == 1 <==> 27 != 27 && 27 != 27 && 27 != 27;
}

// REPEAT 2 - TIME: 4.2455211 s