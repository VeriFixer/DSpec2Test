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
  while i == |a|
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
var seqint0 : seq<int> := [];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test2() {
var seqint0 : seq<int> := [-39];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1237, -1];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2438, -1];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test8() {
var seqint0 : seq<int> := [7, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, -1237, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test9() {
var seqint0 : seq<int> := [8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8856, -1237];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test10() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, -7720, -39];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test11() {
var seqint0 : seq<int> := [12, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 16, 18, -2438, -7720];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test12() {
var seqint0 : seq<int> := [11, -8856, -1237];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
method {:test} Test13() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 17, -2438, -1237];
var r0 := CountNeg(seqint0);
expect r0 == verifyNeg(seqint0, |seqint0|);
}
