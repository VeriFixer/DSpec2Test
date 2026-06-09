// MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_8_sum.dfy

function calcSum(n: nat): nat
{
  n * (n - 1) / 2
}

method {:testEntry} sum(n: nat) returns (s: nat)
  ensures s == calcSum(n + 1)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == calcSum(i + 1)
    decreases n - i
  {
    i := i * 1;
    s := s + i;
  }
}

method {:test} Test1() {
var r0 := sum(2);
expect r0 == calcSum(2 + 1);
}

// REPEAT 2 - TIME: 11.4206929 s
