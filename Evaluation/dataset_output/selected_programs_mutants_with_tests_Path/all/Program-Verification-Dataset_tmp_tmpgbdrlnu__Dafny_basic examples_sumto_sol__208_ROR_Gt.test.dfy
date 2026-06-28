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
  while i > n
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
var r0 := SumUpTo(40);
expect r0 == sum_up_to(40);
}
method {:test} Test1() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (2045 as nat), (5282 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 1 - TIME: 8.5558507 s

method {:test} Test2() {
var r0 := SumUpTo(41);
expect r0 == sum_up_to(41);
}
method {:test} Test3() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (36 as nat), (2 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 2 - TIME: 13.5053247 s

method {:test} Test4() {
var r0 := SumUpTo(42);
expect r0 == sum_up_to(42);
}
method {:test} Test5() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1796 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 3 - TIME: 18.2217351 s

method {:test} Test6() {
var r0 := SumUpTo(43);
expect r0 == sum_up_to(43);
}
method {:test} Test7() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (36 as nat), (2 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 4 - TIME: 23.4370869 s

method {:test} Test8() {
var r0 := SumUpTo(44);
expect r0 == sum_up_to(44);
}
method {:test} Test9() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (36 as nat), (2 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 5 - TIME: 29.1147923 s

method {:test} Test10() {
var r0 := SumUpTo(45);
expect r0 == sum_up_to(45);
}
method {:test} Test11() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (5798 as nat), (1921 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 6 - TIME: 34.7479157 s

method {:test} Test12() {
var r0 := SumUpTo(46);
expect r0 == sum_up_to(46);
}
method {:test} Test13() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (38 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 7 - TIME: 40.3134168 s

method {:test} Test14() {
var r0 := SumUpTo(47);
expect r0 == sum_up_to(47);
}
method {:test} Test15() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (5798 as nat), (1921 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 8 - TIME: 46.026575 s

method {:test} Test16() {
var r0 := SumUpTo(48);
expect r0 == sum_up_to(48);
}
method {:test} Test17() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 9 - TIME: 51.1734028 s

method {:test} Test18() {
var r0 := SumUpTo(49);
expect r0 == sum_up_to(49);
}
method {:test} Test19() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1236 as nat), (7719 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 10 - TIME: 58.5709817 s
