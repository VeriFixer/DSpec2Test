
method {:test} Test11() {
var r0 := CountEqualNumbers(37, 38, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 38 && 38 == 38;
expect r0 == 2 <==> (37 == 38 && 38 != 38) || (37 != 38 && 38 == 38) || (37 == 38 && 38 != 38);
expect r0 == 1 <==> 37 != 38 && 38 != 38 && 37 != 38;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}

// REPEAT 6 - TIME: 8.9656163 s