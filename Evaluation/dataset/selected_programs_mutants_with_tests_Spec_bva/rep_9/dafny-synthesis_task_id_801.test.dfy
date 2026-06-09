
method {:test} Test85() {
var r0 := CountEqualNumbers(55, 55, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 55 && 55 == 55;
expect r0 == 2 <==> (55 == 55 && 55 != 55) || (55 != 55 && 55 == 55) || (55 == 55 && 55 != 55);
expect r0 == 1 <==> 55 != 55 && 55 != 55 && 55 != 55;
}
method {:test} Test86() {
var r0 := CountEqualNumbers(55, 56, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 55 == 56 && 56 == 56;
expect r0 == 2 <==> (55 == 56 && 56 != 56) || (55 != 56 && 56 == 56) || (55 == 56 && 56 != 56);
expect r0 == 1 <==> 55 != 56 && 56 != 56 && 55 != 56;
}
method {:test} Test87() {
var r0 := CountEqualNumbers(56, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 56 == 57 && 57 == 56;
expect r0 == 2 <==> (56 == 57 && 57 != 56) || (56 != 57 && 57 == 56) || (56 == 56 && 57 != 56);
expect r0 == 1 <==> 56 != 57 && 57 != 56 && 56 != 56;
}
method {:test} Test88() {
var r0 := CountEqualNumbers(56, 55, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 56 == 55 && 55 == 57;
expect r0 == 2 <==> (56 == 55 && 55 != 57) || (56 != 55 && 55 == 57) || (56 == 57 && 55 != 57);
expect r0 == 1 <==> 56 != 55 && 55 != 57 && 56 != 57;
}
method {:test} Test89() {
var r0 := CountEqualNumbers(57, 57, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 55;
expect r0 == 2 <==> (57 == 57 && 57 != 55) || (57 != 57 && 57 == 55) || (57 == 55 && 57 != 55);
expect r0 == 1 <==> 57 != 57 && 57 != 55 && 57 != 55;
}

// REPEAT 9 - TIME: 253.1736386 s