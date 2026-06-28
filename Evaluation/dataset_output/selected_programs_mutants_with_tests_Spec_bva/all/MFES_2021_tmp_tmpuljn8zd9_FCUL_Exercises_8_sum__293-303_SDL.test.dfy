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
method {:test} Test1() {
var r0 := sum(100);
expect r0 == calcSum(100 + 1);
}

// REPEAT 1 - TIME: 7.9556367 s

method {:test} Test5() {
var r0 := sum(101);
expect r0 == calcSum(101 + 1);
}

// REPEAT 2 - TIME: 9.3199748 s

method {:test} Test6() {
var r0 := sum(102);
expect r0 == calcSum(102 + 1);
}

// REPEAT 3 - TIME: 10.4381614 s

method {:test} Test7() {
var r0 := sum(103);
expect r0 == calcSum(103 + 1);
}

// REPEAT 4 - TIME: 11.4891526 s

method {:test} Test8() {
var r0 := sum(104);
expect r0 == calcSum(104 + 1);
}

// REPEAT 5 - TIME: 12.3500747 s

method {:test} Test9() {
var r0 := sum(105);
expect r0 == calcSum(105 + 1);
}

// REPEAT 6 - TIME: 13.3519587 s

method {:test} Test10() {
var r0 := sum(106);
expect r0 == calcSum(106 + 1);
}

// REPEAT 7 - TIME: 14.2606251 s

method {:test} Test11() {
var r0 := sum(107);
expect r0 == calcSum(107 + 1);
}

// REPEAT 8 - TIME: 15.1852842 s

method {:test} Test12() {
var r0 := sum(108);
expect r0 == calcSum(108 + 1);
}

// REPEAT 9 - TIME: 16.1380207 s

method {:test} Test13() {
var r0 := sum(109);
expect r0 == calcSum(109 + 1);
}

// REPEAT 10 - TIME: 17.1874066 s
