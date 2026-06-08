
method {:test} Test34() {
var r0 := Max(112, 112);
expect r0 == 112 || r0 == 112;
expect r0 >= 112 && r0 >= 112;
}
method {:test} Test35() {
var r0 := Max(112, 113);
expect r0 == 112 || r0 == 113;
expect r0 >= 112 && r0 >= 113;
}

// REPEAT 9 - TIME: 18.018737 s