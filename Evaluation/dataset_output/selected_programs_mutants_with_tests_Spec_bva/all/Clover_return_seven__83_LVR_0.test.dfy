// Clover_return_seven.dfy

method {:testEntry} M(x: int) returns (seven: int)
  ensures seven == 7
{
  seven := 0;
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

// REPEAT 1 - TIME: 6.5235817 s

method {:test} Test6() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 7.9236584 s

method {:test} Test7() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 9.0691402 s

method {:test} Test8() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 10.1542551 s

method {:test} Test9() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 11.0310387 s

method {:test} Test10() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 11.7873044 s

method {:test} Test11() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 12.6136454 s

method {:test} Test12() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 13.385717 s

method {:test} Test13() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 14.0871652 s

method {:test} Test14() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 14.7105747 s
