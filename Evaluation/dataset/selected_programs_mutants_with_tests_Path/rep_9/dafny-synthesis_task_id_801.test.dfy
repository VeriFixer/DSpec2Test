
method {:test} Test40() {
var r0 := CountEqualNumbers(48, 48, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 48;
expect r0 == 2 <==> (48 == 48 && 48 != 48) || (48 != 48 && 48 == 48) || (48 == 48 && 48 != 48);
expect r0 == 1 <==> 48 != 48 && 48 != 48 && 48 != 48;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(48, 48, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 49;
expect r0 == 2 <==> (48 == 48 && 48 != 49) || (48 != 48 && 48 == 49) || (48 == 49 && 48 != 49);
expect r0 == 1 <==> 48 != 48 && 48 != 49 && 48 != 49;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(49, 48, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 49;
expect r0 == 2 <==> (49 == 48 && 48 != 49) || (49 != 48 && 48 == 49) || (49 == 49 && 48 != 49);
expect r0 == 1 <==> 49 != 48 && 48 != 49 && 49 != 49;
}
method {:test} Test43() {
var r0 := CountEqualNumbers(48, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 49 && 49 == 49;
expect r0 == 2 <==> (48 == 49 && 49 != 49) || (48 != 49 && 49 == 49) || (48 == 49 && 49 != 49);
expect r0 == 1 <==> 48 != 49 && 49 != 49 && 48 != 49;
}
method {:test} Test44() {
var r0 := CountEqualNumbers(49, 48, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 50;
expect r0 == 2 <==> (49 == 48 && 48 != 50) || (49 != 48 && 48 == 50) || (49 == 50 && 48 != 50);
expect r0 == 1 <==> 49 != 48 && 48 != 50 && 49 != 50;
}

// REPEAT 9 - TIME: 66.433114 s