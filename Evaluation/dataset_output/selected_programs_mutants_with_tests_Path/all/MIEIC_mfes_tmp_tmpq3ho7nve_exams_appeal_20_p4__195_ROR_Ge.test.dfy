// MIEIC_mfes_tmp_tmpq3ho7nve_exams_appeal_20_p4.dfy

function F(n: nat): nat
{
  if n <= 2 then
    n
  else
    F(n - 1) + F(n - 3)
}

method {:testEntry} calcF(n: nat) returns (res: nat)
  ensures res == F(n)
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i >= n
    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i + 1) && c == F(i + 2)
    decreases n - i
  {
    a, b, c := b, c, a + c;
    i := i + 1;
  }
  res := a;
}


method {:test} Test0() {
var r0 := calcF(0);
expect r0 == F(0);
}

// REPEAT 1 - TIME: 7.9044377 s

method {:test} Test1() {
var r0 := calcF(2);
expect r0 == F(2);
}

// REPEAT 2 - TIME: 12.6653037 s

method {:test} Test2() {
var r0 := calcF(3);
expect r0 == F(3);
}

// REPEAT 3 - TIME: 17.1040217 s

method {:test} Test3() {
var r0 := calcF(4685);
expect r0 == F(4685);
}

// REPEAT 4 - TIME: 21.3343419 s

method {:test} Test4() {
var r0 := calcF(4686);
expect r0 == F(4686);
}

// REPEAT 5 - TIME: 25.7678957 s

method {:test} Test5() {
var r0 := calcF(4687);
expect r0 == F(4687);
}

// REPEAT 6 - TIME: 30.0324354 s

method {:test} Test6() {
var r0 := calcF(4688);
expect r0 == F(4688);
}

// REPEAT 7 - TIME: 34.1318799 s

method {:test} Test7() {
var r0 := calcF(4689);
expect r0 == F(4689);
}

// REPEAT 8 - TIME: 38.4764124 s

method {:test} Test8() {
var r0 := calcF(4690);
expect r0 == F(4690);
}

// REPEAT 9 - TIME: 42.9921619 s

method {:test} Test9() {
var r0 := calcF(4691);
expect r0 == F(4691);
}

// REPEAT 10 - TIME: 48.1597117 s
