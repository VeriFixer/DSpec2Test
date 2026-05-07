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
