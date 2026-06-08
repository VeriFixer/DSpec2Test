
method {:test} Test35() {
var r0 := CountEqualNumbers(52, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 52;
expect r0 == 2 <==> (52 == 52 && 52 != 52) || (52 != 52 && 52 == 52) || (52 == 52 && 52 != 52);
expect r0 == 1 <==> 52 != 52 && 52 != 52 && 52 != 52;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(53, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 52;
expect r0 == 2 <==> (53 == 52 && 52 != 52) || (53 != 52 && 52 == 52) || (53 == 52 && 52 != 52);
expect r0 == 1 <==> 53 != 52 && 52 != 52 && 53 != 52;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(53, 54, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 53;
expect r0 == 2 <==> (53 == 54 && 54 != 53) || (53 != 54 && 54 == 53) || (53 == 53 && 54 != 53);
expect r0 == 1 <==> 53 != 54 && 54 != 53 && 53 != 53;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(53, 54, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 55;
expect r0 == 2 <==> (53 == 54 && 54 != 55) || (53 != 54 && 54 == 55) || (53 == 55 && 54 != 55);
expect r0 == 1 <==> 53 != 54 && 54 != 55 && 53 != 55;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(52, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 53;
expect r0 == 2 <==> (52 == 52 && 52 != 53) || (52 != 52 && 52 == 53) || (52 == 53 && 52 != 53);
expect r0 == 1 <==> 52 != 52 && 52 != 53 && 52 != 53;
}

// REPEAT 8 - TIME: 107.1421186 s