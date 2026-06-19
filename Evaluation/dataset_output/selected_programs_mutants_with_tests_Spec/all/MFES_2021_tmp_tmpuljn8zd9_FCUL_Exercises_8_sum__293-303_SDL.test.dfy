// MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_8_sum.dfy

function calcSum(n: nat): nat
{
  n * (n - 1) / 2
}

method {:testEntry} sum(n: nat) returns (s: nat)
  ensures s == calcSum(n + 1)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == calcSum(i + 1)
    decreases n - i
  {
    s := s + i;
  }
}


method {:test} Test0() {
var r0 := sum(0);
expect r0 == calcSum(0 + 1);
}

// REPEAT 1 - TIME: 2.677282 s

method {:test} Test1() {
var r0 := sum(1);
expect r0 == calcSum(1 + 1);
}

// REPEAT 2 - TIME: 3.7655273 s

method {:test} Test2() {
var r0 := sum(2);
expect r0 == calcSum(2 + 1);
}

// REPEAT 3 - TIME: 5.0304609 s

method {:test} Test3() {
var r0 := sum(3);
expect r0 == calcSum(3 + 1);
}

// REPEAT 4 - TIME: 5.9505198 s

method {:test} Test4() {
var r0 := sum(4);
expect r0 == calcSum(4 + 1);
}

// REPEAT 5 - TIME: 6.8552652 s

method {:test} Test5() {
var r0 := sum(5);
expect r0 == calcSum(5 + 1);
}

// REPEAT 6 - TIME: 7.7534264 s

method {:test} Test6() {
var r0 := sum(6);
expect r0 == calcSum(6 + 1);
}

// REPEAT 7 - TIME: 8.7661054 s

method {:test} Test7() {
var r0 := sum(7);
expect r0 == calcSum(7 + 1);
}

// REPEAT 8 - TIME: 9.4220655 s

method {:test} Test8() {
var r0 := sum(8);
expect r0 == calcSum(8 + 1);
}

// REPEAT 9 - TIME: 10.0260127 s

method {:test} Test9() {
var r0 := sum(9);
expect r0 == calcSum(9 + 1);
}

// REPEAT 10 - TIME: 10.658317 s
