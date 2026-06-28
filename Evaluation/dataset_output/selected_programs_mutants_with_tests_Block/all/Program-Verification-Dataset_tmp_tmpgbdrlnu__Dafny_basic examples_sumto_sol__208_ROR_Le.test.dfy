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
  while i <= n
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
var r0 := SumUpTo(1);
expect r0 == sum_up_to(1);
}
method {:test} Test1() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (43 as nat), (982 as nat), (1386 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 1 - TIME: 3.3191533 s

method {:test} Test2() {
var r0 := SumUpTo(2);
expect r0 == sum_up_to(2);
}
method {:test} Test3() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (1142 as nat), (4711 as nat), (5439 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 2 - TIME: 4.8397976 s

method {:test} Test4() {
var r0 := SumUpTo(3);
expect r0 == sum_up_to(3);
}
method {:test} Test5() {
var seqnat0 : seq<nat> := [(0 as nat), (1142 as nat), (4711 as nat), (5439 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 3 - TIME: 6.1203941 s

method {:test} Test6() {
var r0 := SumUpTo(4);
expect r0 == sum_up_to(4);
}
method {:test} Test7() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (2756 as nat), (340 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 4 - TIME: 7.4003917 s

method {:test} Test8() {
var r0 := SumUpTo(5);
expect r0 == sum_up_to(5);
}
method {:test} Test9() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (1142 as nat), (4711 as nat), (449 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 5 - TIME: 8.7056296 s

method {:test} Test10() {
var r0 := SumUpTo(6);
expect r0 == sum_up_to(6);
}
method {:test} Test11() {
var seqnat0 : seq<nat> := [(0 as nat), (2872 as nat), (4705 as nat), (658 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 6 - TIME: 10.0173637 s

method {:test} Test12() {
var r0 := SumUpTo(7);
expect r0 == sum_up_to(7);
}
method {:test} Test13() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (1142 as nat), (4711 as nat), (5439 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 7 - TIME: 11.0186032 s

method {:test} Test14() {
var r0 := SumUpTo(8);
expect r0 == sum_up_to(8);
}
method {:test} Test15() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (281 as nat), (7323 as nat), (609 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 8 - TIME: 12.4412516 s

method {:test} Test16() {
var r0 := SumUpTo(9);
expect r0 == sum_up_to(9);
}
method {:test} Test17() {
var seqnat0 : seq<nat> := [(0 as nat), (2872 as nat), (4705 as nat), (658 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 9 - TIME: 13.8485478 s

method {:test} Test18() {
var r0 := SumUpTo(10);
expect r0 == sum_up_to(10);
}
method {:test} Test19() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (2997 as nat), (5948 as nat), (84 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 10 - TIME: 15.0381808 s
