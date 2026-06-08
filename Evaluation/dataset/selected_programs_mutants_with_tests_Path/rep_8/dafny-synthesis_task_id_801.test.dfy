
method {:test} Test35() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(45, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 45;
expect r0 == 2 <==> (45 == 46 && 46 != 45) || (45 != 46 && 46 == 45) || (45 == 45 && 46 != 45);
expect r0 == 1 <==> 45 != 46 && 46 != 45 && 45 != 45;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(47, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 47 == 46 && 46 == 45;
expect r0 == 2 <==> (47 == 46 && 46 != 45) || (47 != 46 && 46 == 45) || (47 == 45 && 46 != 45);
expect r0 == 1 <==> 47 != 46 && 46 != 45 && 47 != 45;
}

// REPEAT 8 - TIME: 56.8993361 s