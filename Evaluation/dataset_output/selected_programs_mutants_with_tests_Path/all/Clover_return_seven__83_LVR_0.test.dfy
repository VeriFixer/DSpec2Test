// Clover_return_seven.dfy

method {:testEntry} M(x: int) returns (seven: int)
  ensures seven == 7
{
  seven := 0;
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

// REPEAT 1 - TIME: 3.7956367 s

method {:test} Test1() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 5.4476305 s

method {:test} Test2() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 7.0295645 s

method {:test} Test3() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 8.6210477 s

method {:test} Test4() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 9.9650858 s

method {:test} Test5() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 11.1603792 s

method {:test} Test6() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 12.265034 s

method {:test} Test7() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 13.2714284 s

method {:test} Test8() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 14.5868974 s

method {:test} Test9() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 15.6159751 s
