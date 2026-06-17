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
  while false
    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
  {
    res := i * res;
    i := i + 1;
  }
}


function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

method {:testEntry} factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    var i := 1;
    res := 1;
    while i < n + 1 
        invariant 0 < i <= n + 1
        invariant res == fact(i - 1) // result satisfies postcondition for every iteration, verification fails without this
    {
        res := i * res;
        i := i + 1;
    }
}

method {:test} Test0() {
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 1 - TIME: 2.5583995 s

method {:test} Test1() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 2 - TIME: 3.4992613 s

method {:test} Test2() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 3 - TIME: 4.4739628 s

method {:test} Test3() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 4 - TIME: 5.2749399 s

method {:test} Test4() {
var r0 := factorial(6);
expect r0 == fact(6);
}

// REPEAT 5 - TIME: 6.1369455 s

method {:test} Test5() {
var r0 := factorial(7);
expect r0 == fact(7);
}

// REPEAT 6 - TIME: 7.1655791 s

method {:test} Test6() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 7 - TIME: 7.9848126 s

method {:test} Test7() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 8 - TIME: 8.6871408 s

method {:test} Test8() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 9 - TIME: 9.4699368 s

method {:test} Test9() {
var r0 := factorial(11);
expect r0 == fact(11);
}

// REPEAT 10 - TIME: 10.2433717 s
