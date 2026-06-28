// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := -(a * b);
}


method {:test} Test0() {
var r0 := Multiply(7719, 0);
expect r0 == 7719 * 0;
}

// REPEAT 1 - TIME: 2.5091246 s

method {:test} Test1() {
var r0 := Multiply(7720, 1);
expect r0 == 7720 * 1;
}

// REPEAT 2 - TIME: 3.5108563 s

method {:test} Test2() {
var r0 := Multiply(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 3 - TIME: 4.584165 s

method {:test} Test3() {
var r0 := Multiply(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 4 - TIME: 5.7146757 s

method {:test} Test4() {
var r0 := Multiply(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 5 - TIME: 6.7511397 s

method {:test} Test5() {
var r0 := Multiply(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 6 - TIME: 7.6761739 s

method {:test} Test6() {
var r0 := Multiply(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 7 - TIME: 8.5845841 s

method {:test} Test7() {
var r0 := Multiply(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 8 - TIME: 9.359805 s

method {:test} Test8() {
var r0 := Multiply(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 9 - TIME: 10.1199154 s

method {:test} Test9() {
var r0 := Multiply(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 10 - TIME: 10.8983075 s
