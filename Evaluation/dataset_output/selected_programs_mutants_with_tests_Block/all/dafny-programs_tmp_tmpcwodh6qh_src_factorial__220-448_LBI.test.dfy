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
  while i < n + 1
    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
  {
    break;
    res := i * res;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := factorial(1);
expect r0 == fact(1);
}

// REPEAT 1 - TIME: 2.0228407 s

method {:test} Test1() {
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 2 - TIME: 2.6355802 s

method {:test} Test2() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 3 - TIME: 3.3103385 s

method {:test} Test3() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 4 - TIME: 4.046032 s

method {:test} Test4() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 5 - TIME: 4.7711087 s

method {:test} Test5() {
var r0 := factorial(6);
expect r0 == fact(6);
}

// REPEAT 6 - TIME: 5.649904 s

method {:test} Test6() {
var r0 := factorial(7);
expect r0 == fact(7);
}

// REPEAT 7 - TIME: 6.4668787 s

method {:test} Test7() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 8 - TIME: 7.1819727 s

method {:test} Test8() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 9 - TIME: 7.8436048 s

method {:test} Test9() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 10 - TIME: 8.4093798 s
