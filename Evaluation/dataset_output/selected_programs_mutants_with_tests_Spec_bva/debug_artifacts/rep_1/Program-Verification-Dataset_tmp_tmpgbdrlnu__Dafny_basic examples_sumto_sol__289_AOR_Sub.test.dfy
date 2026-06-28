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
  while i < n
    invariant 0 <= i <= n
    invariant r == sum_up_to(i)
  {
    r := r - 1;
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
var r0 := SumUpTo(100);
expect r0 == sum_up_to(100);
}
method {:test} Test6() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (0 as nat), (609 as nat), (8365 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}
method {:test} Test7() {
var seqnat0 : seq<nat> := [];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}
method {:test} Test8() {
var seqnat0 : seq<nat> := [(449 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}
method {:test} Test10() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (0 as nat), (8365 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}
method {:test} Test11() {
var seqnat0 : seq<nat> := [(0 as nat), (0 as nat), (47 as nat), (53 as nat)];
var r0 := Total(seqnat0);
expect r0 == total(seqnat0[0 .. |seqnat0|]);
}

// REPEAT 1 - TIME: 13.4772599 s
