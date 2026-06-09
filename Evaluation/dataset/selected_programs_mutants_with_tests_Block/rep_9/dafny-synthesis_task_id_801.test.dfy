
method {:test} Test18() {
var r0 := CountEqualNumbers(43, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 44 && 44 == 44;
expect r0 == 2 <==> (43 == 44 && 44 != 44) || (43 != 44 && 44 == 44) || (43 == 44 && 44 != 44);
expect r0 == 1 <==> 43 != 44 && 44 != 44 && 43 != 44;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(43, 43, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 43;
expect r0 == 2 <==> (43 == 43 && 43 != 43) || (43 != 43 && 43 == 43) || (43 == 43 && 43 != 43);
expect r0 == 1 <==> 43 != 43 && 43 != 43 && 43 != 43;
}

// REPEAT 9 - TIME: 12.2252852 s