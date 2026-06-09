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

// REPEAT 1 - TIME: 4.3697094 s

method {:test} Test6() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 5.2785478 s

method {:test} Test7() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 6.0787267 s

method {:test} Test8() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 6.8474339 s

method {:test} Test9() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 7.4870817 s

method {:test} Test10() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 8.1140602 s

method {:test} Test11() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 8.6491917 s

method {:test} Test12() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 9.1130975 s

method {:test} Test13() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 9.6539198 s

method {:test} Test14() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 10.1436012 s
