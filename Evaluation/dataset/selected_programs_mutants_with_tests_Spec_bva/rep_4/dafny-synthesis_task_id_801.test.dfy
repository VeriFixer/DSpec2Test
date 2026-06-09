
method {:test} Test60() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}
method {:test} Test61() {
var r0 := CountEqualNumbers(38, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 39;
expect r0 == 2 <==> (38 == 39 && 39 != 39) || (38 != 39 && 39 == 39) || (38 == 39 && 39 != 39);
expect r0 == 1 <==> 38 != 39 && 39 != 39 && 38 != 39;
}
method {:test} Test62() {
var r0 := CountEqualNumbers(37, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 37;
expect r0 == 2 <==> (37 == 36 && 36 != 37) || (37 != 36 && 36 == 37) || (37 == 37 && 36 != 37);
expect r0 == 1 <==> 37 != 36 && 36 != 37 && 37 != 37;
}
method {:test} Test63() {
var r0 := CountEqualNumbers(38, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 40;
expect r0 == 2 <==> (38 == 39 && 39 != 40) || (38 != 39 && 39 == 40) || (38 == 40 && 39 != 40);
expect r0 == 1 <==> 38 != 39 && 39 != 40 && 38 != 40;
}
method {:test} Test64() {
var r0 := CountEqualNumbers(36, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 37;
expect r0 == 2 <==> (36 == 36 && 36 != 37) || (36 != 36 && 36 == 37) || (36 == 37 && 36 != 37);
expect r0 == 1 <==> 36 != 36 && 36 != 37 && 36 != 37;
}

// REPEAT 4 - TIME: 207.2685895 s