// dafny-programs_tmp_tmpcwodh6qh_src_factorial.dfy

function fact(n: nat): nat
  ensures fact(n) >= 1
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

method {:testEntry} factorial(n: nat) returns (res: nat)
  ensures res == fact(n)
{
  var i := 1;
  res := 1;
  while i < 1
    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
  {
    res := i * res;
    i := 1;
  }
}


method {:test} Test0() {
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 1 - TIME: 10.6063722 s

method {:test} Test1() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 2 - TIME: 16.0121859 s

method {:test} Test2() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 3 - TIME: 21.3320018 s

method {:test} Test3() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 4 - TIME: 26.4149954 s

method {:test} Test4() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 5 - TIME: 31.7981872 s

method {:test} Test5() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 6 - TIME: 37.2931764 s

method {:test} Test6() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 7 - TIME: 42.6611067 s

method {:test} Test7() {
var r0 := factorial(11);
expect r0 == fact(11);
}

// REPEAT 8 - TIME: 48.493584 s

method {:test} Test8() {
var r0 := factorial(12);
expect r0 == fact(12);
}

// REPEAT 9 - TIME: 55.3221917 s

method {:test} Test9() {
var r0 := factorial(13);
expect r0 == fact(13);
}

// REPEAT 10 - TIME: 61.5325932 s
