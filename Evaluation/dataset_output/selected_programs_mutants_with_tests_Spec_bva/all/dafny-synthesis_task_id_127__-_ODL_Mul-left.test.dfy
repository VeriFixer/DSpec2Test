// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := b;
}


method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test0() {
var r0 := Multiply(7719, 0);
expect r0 == 7719 * 0;
}
method {:test} Test1() {
var r0 := Multiply(-100, 0);
expect r0 == -100 * 0;
}
method {:test} Test2() {
var r0 := Multiply(100, 0);
expect r0 == 100 * 0;
}
method {:test} Test3() {
var r0 := Multiply(0, -100);
expect r0 == 0 * -100;
}
method {:test} Test4() {
var r0 := Multiply(0, 100);
expect r0 == 0 * 100;
}
method {:test} Test6() {
var r0 := Multiply(-100, 1);
expect r0 == -100 * 1;
}
method {:test} Test7() {
var r0 := Multiply(100, 1);
expect r0 == 100 * 1;
}

// REPEAT 1 - TIME: 6.1790811 s

method {:test} Test10() {
var r0 := Multiply(7720, 101);
expect r0 == 7720 * 101;
}

// REPEAT 2 - TIME: 7.3383115 s

method {:test} Test11() {
var r0 := Multiply(7721, 102);
expect r0 == 7721 * 102;
}

// REPEAT 3 - TIME: 8.227953 s

method {:test} Test12() {
var r0 := Multiply(7722, 103);
expect r0 == 7722 * 103;
}

// REPEAT 4 - TIME: 9.0349267 s

method {:test} Test13() {
var r0 := Multiply(7723, 104);
expect r0 == 7723 * 104;
}

// REPEAT 5 - TIME: 9.7066076 s

method {:test} Test14() {
var r0 := Multiply(7724, 105);
expect r0 == 7724 * 105;
}

// REPEAT 6 - TIME: 10.4261702 s

method {:test} Test15() {
var r0 := Multiply(7725, 106);
expect r0 == 7725 * 106;
}

// REPEAT 7 - TIME: 11.0823324 s

method {:test} Test16() {
var r0 := Multiply(7726, 107);
expect r0 == 7726 * 107;
}

// REPEAT 8 - TIME: 11.627193 s

method {:test} Test17() {
var r0 := Multiply(7727, 108);
expect r0 == 7727 * 108;
}

// REPEAT 9 - TIME: 12.1943047 s

method {:test} Test18() {
var r0 := Multiply(7728, 109);
expect r0 == 7728 * 109;
}

// REPEAT 10 - TIME: 12.7162854 s
