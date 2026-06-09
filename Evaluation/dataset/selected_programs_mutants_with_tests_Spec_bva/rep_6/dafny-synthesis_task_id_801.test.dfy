
method {:test} Test70() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test71() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test72() {
var r0 := CountEqualNumbers(46, 45, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 46;
expect r0 == 2 <==> (46 == 45 && 45 != 46) || (46 != 45 && 45 == 46) || (46 == 46 && 45 != 46);
expect r0 == 1 <==> 46 != 45 && 45 != 46 && 46 != 46;
}
method {:test} Test73() {
var r0 := CountEqualNumbers(46, 47, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 47 && 47 == 48;
expect r0 == 2 <==> (46 == 47 && 47 != 48) || (46 != 47 && 47 == 48) || (46 == 48 && 47 != 48);
expect r0 == 1 <==> 46 != 47 && 47 != 48 && 46 != 48;
}
method {:test} Test74() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}

// REPEAT 6 - TIME: 225.6194709 s