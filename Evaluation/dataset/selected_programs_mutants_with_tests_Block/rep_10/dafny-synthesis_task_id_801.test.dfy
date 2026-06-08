
method {:test} Test20() {
var r0 := CountEqualNumbers(45, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 46;
expect r0 == 2 <==> (45 == 46 && 46 != 46) || (45 != 46 && 46 == 46) || (45 == 46 && 46 != 46);
expect r0 == 1 <==> 45 != 46 && 46 != 46 && 45 != 46;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(45, 45, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 46;
expect r0 == 2 <==> (45 == 45 && 45 != 46) || (45 != 45 && 45 == 46) || (45 == 46 && 45 != 46);
expect r0 == 1 <==> 45 != 45 && 45 != 46 && 45 != 46;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(45, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 45;
expect r0 == 2 <==> (45 == 46 && 46 != 45) || (45 != 46 && 46 == 45) || (45 == 45 && 46 != 45);
expect r0 == 1 <==> 45 != 46 && 46 != 45 && 45 != 45;
}

// REPEAT 10 - TIME: 14.2993405 s