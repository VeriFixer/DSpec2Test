// Clover_return_seven.dfy

method {:testEntry} M(x: int) returns (seven: int)
  ensures seven == 7
{
  seven := 6;
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

// REPEAT 1 - TIME: 1.9721109 s

method {:test} Test1() {
var r0 := M(24);
expect r0 == 7;
}

// REPEAT 2 - TIME: 2.7364262 s

method {:test} Test2() {
var r0 := M(25);
expect r0 == 7;
}

// REPEAT 3 - TIME: 3.7128399 s

method {:test} Test3() {
var r0 := M(26);
expect r0 == 7;
}

// REPEAT 4 - TIME: 4.41719 s

method {:test} Test4() {
var r0 := M(27);
expect r0 == 7;
}

// REPEAT 5 - TIME: 5.0660394 s

method {:test} Test5() {
var r0 := M(28);
expect r0 == 7;
}

// REPEAT 6 - TIME: 5.8210371 s

method {:test} Test6() {
var r0 := M(29);
expect r0 == 7;
}

// REPEAT 7 - TIME: 6.4616093 s

method {:test} Test7() {
var r0 := M(30);
expect r0 == 7;
}

// REPEAT 8 - TIME: 7.1128425 s

method {:test} Test8() {
var r0 := M(31);
expect r0 == 7;
}

// REPEAT 9 - TIME: 7.7511417 s

method {:test} Test9() {
var r0 := M(32);
expect r0 == 7;
}

// REPEAT 10 - TIME: 8.3487459 s
