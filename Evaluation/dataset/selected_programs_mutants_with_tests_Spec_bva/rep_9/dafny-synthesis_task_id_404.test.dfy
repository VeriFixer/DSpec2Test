
method {:test} Test34() {
var r0 := Min(112, 112);
expect r0 == 112 || r0 == 112;
expect r0 <= 112 && r0 <= 112;
}
method {:test} Test35() {
var r0 := Min(113, 112);
expect r0 == 113 || r0 == 112;
expect r0 <= 113 && r0 <= 112;
}

// REPEAT 9 - TIME: 16.360184 s