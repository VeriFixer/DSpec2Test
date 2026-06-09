
method {:test} Test24() {
var r0 := Min(105, 104);
expect 105 <= 104 ==> r0 == 105;
expect 105 > 104 ==> r0 == 104;
}
method {:test} Test25() {
var r0 := Min(105, 105);
expect 105 <= 105 ==> r0 == 105;
expect 105 > 105 ==> r0 == 105;
}

// REPEAT 4 - TIME: 17.073272 s