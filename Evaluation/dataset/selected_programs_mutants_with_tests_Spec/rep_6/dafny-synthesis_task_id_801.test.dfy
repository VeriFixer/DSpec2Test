
method {:test} Test25() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(45, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 46;
expect r0 == 2 <==> (45 == 46 && 46 != 46) || (45 != 46 && 46 == 46) || (45 == 46 && 46 != 46);
expect r0 == 1 <==> 45 != 46 && 46 != 46 && 45 != 46;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(45, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 44 && 44 == 45;
expect r0 == 2 <==> (45 == 44 && 44 != 45) || (45 != 44 && 44 == 45) || (45 == 45 && 44 != 45);
expect r0 == 1 <==> 45 != 44 && 44 != 45 && 45 != 45;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(45, 46, 47);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 47;
expect r0 == 2 <==> (45 == 46 && 46 != 47) || (45 != 46 && 46 == 47) || (45 == 47 && 46 != 47);
expect r0 == 1 <==> 45 != 46 && 46 != 47 && 45 != 47;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(44, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 44 && 44 == 45;
expect r0 == 2 <==> (44 == 44 && 44 != 45) || (44 != 44 && 44 == 45) || (44 == 45 && 44 != 45);
expect r0 == 1 <==> 44 != 44 && 44 != 45 && 44 != 45;
}

// REPEAT 6 - TIME: 90.5346808 s