// Clover_return_seven.dfy

method {:testEntry} M(x: int) returns (seven: int)
  ensures seven == 7
{
  seven := 8;
}


method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test0() {
var r0 := M(0);
expect r0 == 7;
}
method {:test} Test1() {
var r0 := M(-100);
expect r0 == 7;
}
method {:test} Test2() {
var r0 := M(100);
expect r0 == 7;
}

// REPEAT 1 - TIME: 5.0966157 s

method {:test} Test6() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 5.9757524 s

method {:test} Test7() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 7.0540823 s

method {:test} Test8() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 8.0187341 s

method {:test} Test9() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 9.0665782 s

method {:test} Test10() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 9.8003015 s

method {:test} Test11() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 10.7177038 s

method {:test} Test12() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 11.4315947 s

method {:test} Test13() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 12.0906143 s

method {:test} Test14() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 12.6741012 s
