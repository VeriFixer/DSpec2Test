method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 0);
expect r0 == (0 + 0) / 2;
}

// REPEAT 1 - TIME: 1.7829847 s

method {:test} Test1() {
var r0 := ComputeAvg(17712, 2);
expect r0 == (17712 + 2) / 2;
}

// REPEAT 2 - TIME: 2.431895 s

method {:test} Test2() {
var r0 := ComputeAvg(17713, 3);
expect r0 == (17713 + 3) / 2;
}

// REPEAT 3 - TIME: 3.0536096 s

method {:test} Test3() {
var r0 := ComputeAvg(17714, 4);
expect r0 == (17714 + 4) / 2;
}

// REPEAT 4 - TIME: 3.7173819 s

method {:test} Test4() {
var r0 := ComputeAvg(17715, 5);
expect r0 == (17715 + 5) / 2;
}

// REPEAT 5 - TIME: 4.3660188 s

method {:test} Test5() {
var r0 := ComputeAvg(17716, 6);
expect r0 == (17716 + 6) / 2;
}

// REPEAT 6 - TIME: 5.0339606 s

method {:test} Test6() {
var r0 := ComputeAvg(17718, 8);
expect r0 == (17718 + 8) / 2;
}

// REPEAT 7 - TIME: 5.6126797 s

method {:test} Test7() {
var r0 := ComputeAvg(17719, 9);
expect r0 == (17719 + 9) / 2;
}

// REPEAT 8 - TIME: 6.210623 s

method {:test} Test8() {
var r0 := ComputeAvg(17720, 10);
expect r0 == (17720 + 10) / 2;
}

// REPEAT 9 - TIME: 6.7291634 s

method {:test} Test9() {
var r0 := ComputeAvg(17722, 12);
expect r0 == (17722 + 12) / 2;
}

// REPEAT 10 - TIME: 7.2439992 s
