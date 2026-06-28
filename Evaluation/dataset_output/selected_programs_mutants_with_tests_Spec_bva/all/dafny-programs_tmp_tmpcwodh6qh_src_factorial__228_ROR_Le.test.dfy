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
method {:test} Test1() {
var r0 := factorial(100);
expect r0 == fact(100);
}
method {:test} Test3() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 1 - TIME: 7.6029187 s

method {:test} Test6() {
var r0 := factorial(101);
expect r0 == fact(101);
}

// REPEAT 2 - TIME: 8.9939387 s

method {:test} Test7() {
var r0 := factorial(102);
expect r0 == fact(102);
}

// REPEAT 3 - TIME: 10.007802 s

method {:test} Test8() {
var r0 := factorial(103);
expect r0 == fact(103);
}

// REPEAT 4 - TIME: 11.1793282 s

method {:test} Test9() {
var r0 := factorial(104);
expect r0 == fact(104);
}

// REPEAT 5 - TIME: 12.1430855 s

method {:test} Test10() {
var r0 := factorial(105);
expect r0 == fact(105);
}

// REPEAT 6 - TIME: 13.1942917 s

method {:test} Test11() {
var r0 := factorial(106);
expect r0 == fact(106);
}

// REPEAT 7 - TIME: 14.4504914 s

method {:test} Test12() {
var r0 := factorial(107);
expect r0 == fact(107);
}

// REPEAT 8 - TIME: 15.4528786 s

method {:test} Test13() {
var r0 := factorial(108);
expect r0 == fact(108);
}

// REPEAT 9 - TIME: 16.3741258 s

method {:test} Test14() {
var r0 := factorial(109);
expect r0 == fact(109);
}

// REPEAT 10 - TIME: 17.2689631 s
