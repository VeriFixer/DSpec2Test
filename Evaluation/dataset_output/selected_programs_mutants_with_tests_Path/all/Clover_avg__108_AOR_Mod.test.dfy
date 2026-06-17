// Clover_avg.dfy

method {:testEntry} ComputeAvg(a: int, b: int) returns (avg: int)
  ensures avg == (a + b) / 2
{
  avg := (a + b) % 2;
}


method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 0);
expect r0 == (0 + 0) / 2;
}

// REPEAT 1 - TIME: 3.4370868 s

method {:test} Test1() {
var r0 := ComputeAvg(17712, 2);
expect r0 == (17712 + 2) / 2;
}

// REPEAT 2 - TIME: 4.6392148 s

method {:test} Test2() {
var r0 := ComputeAvg(17713, 3);
expect r0 == (17713 + 3) / 2;
}

// REPEAT 3 - TIME: 6.2543477 s

method {:test} Test3() {
var r0 := ComputeAvg(17714, 4);
expect r0 == (17714 + 4) / 2;
}

// REPEAT 4 - TIME: 7.74085 s

method {:test} Test4() {
var r0 := ComputeAvg(17715, 5);
expect r0 == (17715 + 5) / 2;
}

// REPEAT 5 - TIME: 9.4846987 s

method {:test} Test5() {
var r0 := ComputeAvg(17716, 6);
expect r0 == (17716 + 6) / 2;
}

// REPEAT 6 - TIME: 10.9280841 s

method {:test} Test6() {
var r0 := ComputeAvg(17718, 8);
expect r0 == (17718 + 8) / 2;
}

// REPEAT 7 - TIME: 12.2369425 s

method {:test} Test7() {
var r0 := ComputeAvg(17719, 9);
expect r0 == (17719 + 9) / 2;
}

// REPEAT 8 - TIME: 13.3514916 s

method {:test} Test8() {
var r0 := ComputeAvg(17720, 10);
expect r0 == (17720 + 10) / 2;
}

// REPEAT 9 - TIME: 14.7145082 s

method {:test} Test9() {
var r0 := ComputeAvg(17722, 12);
expect r0 == (17722 + 12) / 2;
}

// REPEAT 10 - TIME: 15.9701114 s
