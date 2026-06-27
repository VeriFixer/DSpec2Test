// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_ComputePower.dfy

function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method {:testEntry} ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while i >= n
    invariant 0 <= i <= n && p == Power(i)
  {
    i := i + 1;
    p := p * 2;
  }
}


method {:test} Test0() {
var r0 := ComputePower(8367);
expect r0 == Power(8367);
}

// REPEAT 1 - TIME: 14.3463462 s

method {:test} Test1() {
var r0 := ComputePower(8368);
expect r0 == Power(8368);
}

// REPEAT 2 - TIME: 24.6312196 s

method {:test} Test2() {
var r0 := ComputePower(8369);
expect r0 == Power(8369);
}

// REPEAT 3 - TIME: 34.4970235 s

method {:test} Test3() {
var r0 := ComputePower(8370);
expect r0 == Power(8370);
}

// REPEAT 4 - TIME: 45.5780117 s

method {:test} Test4() {
var r0 := ComputePower(8371);
expect r0 == Power(8371);
}

// REPEAT 5 - TIME: 56.0864798 s

method {:test} Test5() {
var r0 := ComputePower(8372);
expect r0 == Power(8372);
}

// REPEAT 6 - TIME: 69.0013425 s

method {:test} Test6() {
var r0 := ComputePower(8373);
expect r0 == Power(8373);
}

// REPEAT 7 - TIME: 82.060534 s

method {:test} Test7() {
var r0 := ComputePower(8374);
expect r0 == Power(8374);
}

// REPEAT 8 - TIME: 93.4386288 s

method {:test} Test8() {
var r0 := ComputePower(8375);
expect r0 == Power(8375);
}

// REPEAT 9 - TIME: 106.4960972 s

method {:test} Test9() {
var r0 := ComputePower(8376);
expect r0 == Power(8376);
}

// REPEAT 10 - TIME: 121.178603 s
