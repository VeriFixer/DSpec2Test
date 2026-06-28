// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := a + b - 2;
}


method {:test} Test0() {
var r0 := ComputeAvg(0, 0);
expect r0 == (0 + 0) / 2;
}

// REPEAT 1 - TIME: 3.5601225 s

method {:test} Test1() {
var r0 := ComputeAvg(17712, 2);
expect r0 == (17712 + 2) / 2;
}

// REPEAT 2 - TIME: 4.9955583 s

method {:test} Test2() {
var r0 := ComputeAvg(17713, 3);
expect r0 == (17713 + 3) / 2;
}

// REPEAT 3 - TIME: 6.5610055 s

method {:test} Test3() {
var r0 := ComputeAvg(17714, 4);
expect r0 == (17714 + 4) / 2;
}

// REPEAT 4 - TIME: 8.1989591 s

method {:test} Test4() {
var r0 := ComputeAvg(17715, 5);
expect r0 == (17715 + 5) / 2;
}

// REPEAT 5 - TIME: 9.7434393 s

method {:test} Test5() {
var r0 := ComputeAvg(17716, 6);
expect r0 == (17716 + 6) / 2;
}

// REPEAT 6 - TIME: 11.4343494 s

method {:test} Test6() {
var r0 := ComputeAvg(17717, 7);
expect r0 == (17717 + 7) / 2;
}

// REPEAT 7 - TIME: 12.9694363 s

method {:test} Test7() {
var r0 := ComputeAvg(17718, 8);
expect r0 == (17718 + 8) / 2;
}

// REPEAT 8 - TIME: 14.5986117 s

method {:test} Test8() {
var r0 := ComputeAvg(17719, 9);
expect r0 == (17719 + 9) / 2;
}

// REPEAT 9 - TIME: 15.9780723 s

method {:test} Test9() {
var r0 := ComputeAvg(17720, 10);
expect r0 == (17720 + 10) / 2;
}

// REPEAT 10 - TIME: 17.158856 s
