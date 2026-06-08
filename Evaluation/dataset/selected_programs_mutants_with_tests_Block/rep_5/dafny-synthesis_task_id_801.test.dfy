
method {:test} Test9() {
var r0 := CountEqualNumbers(36, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 35 && 35 == 35;
expect r0 == 2 <==> (36 == 35 && 35 != 35) || (36 != 35 && 35 == 35) || (36 == 35 && 35 != 35);
expect r0 == 1 <==> 36 != 35 && 35 != 35 && 36 != 35;
}
method {:test} Test10() {
var r0 := CountEqualNumbers(34, 34, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 34;
expect r0 == 2 <==> (34 == 34 && 34 != 34) || (34 != 34 && 34 == 34) || (34 == 34 && 34 != 34);
expect r0 == 1 <==> 34 != 34 && 34 != 34 && 34 != 34;
}

// REPEAT 5 - TIME: 8.2558013 s