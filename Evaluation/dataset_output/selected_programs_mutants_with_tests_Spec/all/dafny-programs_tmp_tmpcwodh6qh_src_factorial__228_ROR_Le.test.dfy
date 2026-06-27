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
  while i <= n + 1
    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
  {
    res := i * res;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 1 - TIME: 3.0119107 s

method {:test} Test1() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 2 - TIME: 4.096353 s

method {:test} Test2() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 3 - TIME: 5.2643198 s

method {:test} Test3() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 4 - TIME: 6.3283465 s

method {:test} Test4() {
var r0 := factorial(6);
expect r0 == fact(6);
}

// REPEAT 5 - TIME: 7.3036835 s

method {:test} Test5() {
var r0 := factorial(7);
expect r0 == fact(7);
}

// REPEAT 6 - TIME: 8.3199636 s

method {:test} Test6() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 7 - TIME: 9.1197842 s

method {:test} Test7() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 8 - TIME: 9.983194 s

method {:test} Test8() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 9 - TIME: 10.7078512 s

method {:test} Test9() {
var r0 := factorial(11);
expect r0 == fact(11);
}

// REPEAT 10 - TIME: 11.434229 s
