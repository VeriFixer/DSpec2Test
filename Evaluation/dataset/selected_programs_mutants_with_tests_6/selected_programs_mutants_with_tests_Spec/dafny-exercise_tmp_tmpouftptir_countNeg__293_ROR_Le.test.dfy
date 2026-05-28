// dafny-exercise_tmp_tmpouftptir_countNeg.dfy

function verifyNeg(a: seq<int>, idx: int): nat
  requires 0 <= idx <= |a|
{
  if idx == 0 then
    0
  else
    verifyNeg(a, idx - 1) + if a[idx - 1] < 0 then 1 else 0
}

method {:testEntry} CountNeg(a: seq<int>) returns (cnt: nat)
  ensures cnt == verifyNeg(a, |a|)
{
  var i := 0;
  cnt := 0;
  while i <= |a|
    invariant 0 <= i <= |a|
    invariant cnt == verifyNeg(a, i)
  {
    if a[i] < 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1237, -1];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test1() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2438, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test2() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2438, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test3() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1237, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test4() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2438, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test5() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 10, 12, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1237, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
