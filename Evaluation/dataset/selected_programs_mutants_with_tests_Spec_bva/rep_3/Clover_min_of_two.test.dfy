
method {:test} Test22() {
var r0 := Min(104, 103);
expect 104 <= 103 ==> r0 == 104;
expect 104 > 103 ==> r0 == 103;
}
method {:test} Test23() {
var r0 := Min(103, 103);
expect 103 <= 103 ==> r0 == 103;
expect 103 > 103 ==> r0 == 103;
}

// REPEAT 3 - TIME: 15.8839589 s