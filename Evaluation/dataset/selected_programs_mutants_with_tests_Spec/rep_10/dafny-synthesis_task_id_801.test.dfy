
method {:test} Test45() {
var r0 := CountEqualNumbers(60, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 60;
expect r0 == 2 <==> (60 == 60 && 60 != 60) || (60 != 60 && 60 == 60) || (60 == 60 && 60 != 60);
expect r0 == 1 <==> 60 != 60 && 60 != 60 && 60 != 60;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(61, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 60;
expect r0 == 2 <==> (61 == 60 && 60 != 60) || (61 != 60 && 60 == 60) || (61 == 60 && 60 != 60);
expect r0 == 1 <==> 61 != 60 && 60 != 60 && 61 != 60;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(61, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 61;
expect r0 == 2 <==> (61 == 60 && 60 != 61) || (61 != 60 && 60 == 61) || (61 == 61 && 60 != 61);
expect r0 == 1 <==> 61 != 60 && 60 != 61 && 61 != 61;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(62, 61, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 60;
expect r0 == 2 <==> (62 == 61 && 61 != 60) || (62 != 61 && 61 == 60) || (62 == 60 && 61 != 60);
expect r0 == 1 <==> 62 != 61 && 61 != 60 && 62 != 60;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(60, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 61;
expect r0 == 2 <==> (60 == 60 && 60 != 61) || (60 != 60 && 60 == 61) || (60 == 61 && 60 != 61);
expect r0 == 1 <==> 60 != 60 && 60 != 61 && 60 != 61;
}

// REPEAT 10 - TIME: 145.3479297 s