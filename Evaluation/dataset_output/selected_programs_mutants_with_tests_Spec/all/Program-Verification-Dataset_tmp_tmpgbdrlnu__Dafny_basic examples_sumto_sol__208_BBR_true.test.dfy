// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_sumto_sol.dfy

function sum_up_to(n: nat): nat
{
  if n == 0 then
    0
  else
    sum_up_to(n - 1) + 1
}

method {:testEntry} SumUpTo(n: nat) returns (r: nat)
  ensures r == sum_up_to(n)
{
  var i := 0;
  r := 0;
  while true
    invariant 0 <= i <= n
    invariant r == sum_up_to(i)
  {
    r := r + 1;
    i := i + 1;
  }
}

function total(a: seq<nat>): nat
{
  if |a| == 0 then
    0
  else
    total(a[0 .. |a| - 1]) + a[|a| - 1]
}

lemma total_lemma(a: seq<nat>, i: nat)
  requires |a| > 0
  requires 0 <= i < |a|
  ensures total(a[0 .. i]) + a[i] == total(a[0 .. i + 1])
{
  ghost var b := a[0 .. i + 1];
  calc {
    total(a[0 .. i + 1]);
    total(b);
    total(b[0 .. |b| - 1]) + b[|b| - 1];
    total(b[0 .. |b| - 1]) + a[i];
    {
      assert b[0 .. |b| - 1] == a[0 .. i];
    }
    total(a[0 .. i]) + a[i];
  }
}

method {:testEntry} Total(a: seq<nat>) returns (r: nat)
  ensures r == total(a[0 .. |a|])
{
  var i := 0;
  r := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant r == total(a[0 .. i])
  {
    total_lemma(a, i);
    r := r + a[i];
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := SumUpTo(7721);
expect r0 == sum_up_to(7721);
}
method {:test} Test1() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (609 as nat), (8365 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 1 - TIME: 3.8314789 s

method {:test} Test2() {
var r0 := SumUpTo(7722);
expect r0 == sum_up_to(7722);
}
method {:test} Test3() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 2 - TIME: 4.9745385 s

method {:test} Test4() {
var r0 := SumUpTo(7723);
expect r0 == sum_up_to(7723);
}
method {:test} Test5() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (5798 as nat), (1921 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 3 - TIME: 6.3041317 s

method {:test} Test6() {
var r0 := SumUpTo(7724);
expect r0 == sum_up_to(7724);
}
method {:test} Test7() {
var seqnat0 : seq<nat> := [];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 4 - TIME: 7.7131176 s

method {:test} Test8() {
var r0 := SumUpTo(7725);
expect r0 == sum_up_to(7725);
}
method {:test} Test9() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 5 - TIME: 9.1919998 s

method {:test} Test10() {
var r0 := SumUpTo(7726);
expect r0 == sum_up_to(7726);
}
method {:test} Test11() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (38 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 6 - TIME: 10.5538551 s

method {:test} Test12() {
var r0 := SumUpTo(7727);
expect r0 == sum_up_to(7727);
}
method {:test} Test13() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 7 - TIME: 11.7163624 s

method {:test} Test14() {
var r0 := SumUpTo(7728);
expect r0 == sum_up_to(7728);
}
method {:test} Test15() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 8 - TIME: 12.859656 s

method {:test} Test16() {
var r0 := SumUpTo(7729);
expect r0 == sum_up_to(7729);
}
method {:test} Test17() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 9 - TIME: 14.1753715 s

method {:test} Test18() {
var r0 := SumUpTo(7730);
expect r0 == sum_up_to(7730);
}
method {:test} Test19() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 10 - TIME: 15.1840249 s
