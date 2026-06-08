method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test0() {
var r0 := M(0);
expect r0 == 7;
}

// REPEAT 1 - TIME: 2.9613146 s

method {:test} Test1() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 4.1220602 s

method {:test} Test2() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 5.2263781 s

method {:test} Test3() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 6.3642197 s

method {:test} Test4() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 7.3839621 s

method {:test} Test5() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 8.2361182 s

method {:test} Test6() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 9.1395861 s

method {:test} Test7() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 10.0467857 s

method {:test} Test8() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 10.8135003 s

method {:test} Test9() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 11.9006872 s
