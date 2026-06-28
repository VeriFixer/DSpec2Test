// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_sum.dfy

ghost function sum(n: nat): int
{
  if n == 0 then
    0
  else
    n + sum(n - 1)
}

method {:testEntry} Sum(n: nat) returns (s: int)
  ensures s == sum(n)
{
  var x: nat := 0;
  var y: nat := 1;
  var k: nat := n;
  while k <= 0
    invariant sum(n) == x + y * sum(k)
    invariant 0 <= k <= n
    decreases k
  {
    assert sum(n) == x + y * sum(k);
    assert sum(n) == x + y * (k + sum(k - 1));
    assert sum(n) == x + y * k + y * sum(k - 1);
    x := x + y * k;
    assert sum(n) == x + y * sum(k - 1);
    assert sum(n) == x + y * sum(k - 1);
    k := k - 1;
    assert sum(n) == x + y * sum(k);
  }
  assert k == 0;
  assert sum(n) == x + y * sum(0);
  assert sum(n) == x + y * 0;
  s := x;
  assert sum(n) == s;
}


method {:test} Test0() {
var r0 := Sum(7721);
}

// REPEAT 1 - TIME: 2.4815892 s

method {:test} Test1() {
var r0 := Sum(7722);
}

// REPEAT 2 - TIME: 3.5512585 s

method {:test} Test2() {
var r0 := Sum(7723);
}

// REPEAT 3 - TIME: 4.9787716 s

method {:test} Test3() {
var r0 := Sum(7724);
}

// REPEAT 4 - TIME: 6.0995446 s

method {:test} Test4() {
var r0 := Sum(7725);
}

// REPEAT 5 - TIME: 7.2333616 s

method {:test} Test5() {
var r0 := Sum(7726);
}

// REPEAT 6 - TIME: 8.1565886 s

method {:test} Test6() {
var r0 := Sum(7727);
}

// REPEAT 7 - TIME: 9.0831277 s

method {:test} Test7() {
var r0 := Sum(7728);
}

// REPEAT 8 - TIME: 10.1515412 s

method {:test} Test8() {
var r0 := Sum(7729);
}

// REPEAT 9 - TIME: 11.0336507 s

method {:test} Test9() {
var r0 := Sum(7730);
}

// REPEAT 10 - TIME: 11.8490142 s
