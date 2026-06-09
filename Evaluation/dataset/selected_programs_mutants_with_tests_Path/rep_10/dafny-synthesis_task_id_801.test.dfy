
method {:test} Test45() {
var r0 := CountEqualNumbers(51, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 51;
expect r0 == 2 <==> (51 == 51 && 51 != 51) || (51 != 51 && 51 == 51) || (51 == 51 && 51 != 51);
expect r0 == 1 <==> 51 != 51 && 51 != 51 && 51 != 51;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(52, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 51;
expect r0 == 2 <==> (52 == 52 && 52 != 51) || (52 != 52 && 52 == 51) || (52 == 51 && 52 != 51);
expect r0 == 1 <==> 52 != 52 && 52 != 51 && 52 != 51;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(51, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 52 && 52 == 51;
expect r0 == 2 <==> (51 == 52 && 52 != 51) || (51 != 52 && 52 == 51) || (51 == 51 && 52 != 51);
expect r0 == 1 <==> 51 != 52 && 52 != 51 && 51 != 51;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(52, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 51 && 51 == 51;
expect r0 == 2 <==> (52 == 51 && 51 != 51) || (52 != 51 && 51 == 51) || (52 == 51 && 51 != 51);
expect r0 == 1 <==> 52 != 51 && 51 != 51 && 52 != 51;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(53, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 51;
expect r0 == 2 <==> (53 == 52 && 52 != 51) || (53 != 52 && 52 == 51) || (53 == 51 && 52 != 51);
expect r0 == 1 <==> 53 != 52 && 52 != 51 && 53 != 51;
}

// REPEAT 10 - TIME: 42.9439539 s