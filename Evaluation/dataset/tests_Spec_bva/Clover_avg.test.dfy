method {:testEntry} ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  avg:= (a + b) / 2;
}

method {:test} Test0() {
var r0 := ComputeAvg(0, 1);
expect r0 == (0 + 1) / 2;
}
method {:test} Test1() {
var r0 := ComputeAvg(-100, 101);
expect r0 == (-100 + 101) / 2;
}
method {:test} Test2() {
var r0 := ComputeAvg(100, -100);
expect r0 == (100 + -100) / 2;
}
method {:test} Test3() {
var r0 := ComputeAvg(101, -100);
expect r0 == (101 + -100) / 2;
}
method {:test} Test4() {
var r0 := ComputeAvg(-100, 100);
expect r0 == (-100 + 100) / 2;
}
method {:test} Test6() {
var r0 := ComputeAvg(-200, 0);
expect r0 == (-200 + 0) / 2;
}
method {:test} Test7() {
var r0 := ComputeAvg(200, 0);
expect r0 == (200 + 0) / 2;
}
method {:test} Test8() {
var r0 := ComputeAvg(0, 1236);
expect r0 == (0 + 1236) / 2;
}
method {:test} Test9() {
var r0 := ComputeAvg(0, 0);
expect r0 == (0 + 0) / 2;
}

// REPEAT 1 - TIME: 6.1072666 s

method {:test} Test10() {
var r0 := ComputeAvg(202, 1238);
expect r0 == (202 + 1238) / 2;
}

// REPEAT 2 - TIME: 7.0059772 s

method {:test} Test11() {
var r0 := ComputeAvg(204, 1240);
expect r0 == (204 + 1240) / 2;
}

// REPEAT 3 - TIME: 7.8844597 s

method {:test} Test12() {
var r0 := ComputeAvg(206, 1242);
expect r0 == (206 + 1242) / 2;
}

// REPEAT 4 - TIME: 8.7254827 s

method {:test} Test13() {
var r0 := ComputeAvg(208, 1244);
expect r0 == (208 + 1244) / 2;
}

// REPEAT 5 - TIME: 9.418835 s

method {:test} Test14() {
var r0 := ComputeAvg(210, 1246);
expect r0 == (210 + 1246) / 2;
}

// REPEAT 6 - TIME: 10.0917023 s

method {:test} Test15() {
var r0 := ComputeAvg(212, 1248);
expect r0 == (212 + 1248) / 2;
}

// REPEAT 7 - TIME: 10.7847288 s

method {:test} Test16() {
var r0 := ComputeAvg(214, 1250);
expect r0 == (214 + 1250) / 2;
}

// REPEAT 8 - TIME: 11.5038345 s

method {:test} Test17() {
var r0 := ComputeAvg(216, 1252);
expect r0 == (216 + 1252) / 2;
}

// REPEAT 9 - TIME: 12.1299215 s

method {:test} Test18() {
var r0 := ComputeAvg(218, 1254);
expect r0 == (218 + 1254) / 2;
}

// REPEAT 10 - TIME: 12.7259948 s
