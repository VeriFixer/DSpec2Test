method {:testEntry} M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}

method {:test} Test0() {
var r0 := M(0);
expect r0 == 7;
}

// REPEAT 1 - TIME: 2.0159879 s

method {:test} Test1() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 2.5695422 s

method {:test} Test2() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 3.1742085 s

method {:test} Test3() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 3.8111373 s

method {:test} Test4() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 4.3734425 s

method {:test} Test5() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 5.0442792 s

method {:test} Test6() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 5.619107 s

method {:test} Test7() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 6.2401336 s

method {:test} Test8() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 6.7914814 s

method {:test} Test9() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 7.3534462 s
