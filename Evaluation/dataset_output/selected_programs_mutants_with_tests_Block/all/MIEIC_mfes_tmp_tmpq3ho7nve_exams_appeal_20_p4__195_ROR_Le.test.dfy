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
  while i <= n
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

// REPEAT 1 - TIME: 2.3269199 s

method {:test} Test1() {
var r0 := calcF(1);
expect r0 == F(1);
}

// REPEAT 2 - TIME: 3.385787 s

method {:test} Test2() {
var r0 := calcF(5);
expect r0 == F(5);
}

// REPEAT 3 - TIME: 4.3745881 s

method {:test} Test3() {
var r0 := calcF(4685);
expect r0 == F(4685);
}

// REPEAT 4 - TIME: 5.1896439 s

method {:test} Test4() {
var r0 := calcF(4686);
expect r0 == F(4686);
}

// REPEAT 5 - TIME: 6.0362952 s

method {:test} Test5() {
var r0 := calcF(4687);
expect r0 == F(4687);
}

// REPEAT 6 - TIME: 6.8353782 s

method {:test} Test6() {
var r0 := calcF(4688);
expect r0 == F(4688);
}

// REPEAT 7 - TIME: 7.6059539 s

method {:test} Test7() {
var r0 := calcF(4689);
expect r0 == F(4689);
}

// REPEAT 8 - TIME: 8.2922848 s

method {:test} Test8() {
var r0 := calcF(4690);
expect r0 == F(4690);
}

// REPEAT 9 - TIME: 9.086689 s

method {:test} Test9() {
var r0 := calcF(4691);
expect r0 == F(4691);
}

// REPEAT 10 - TIME: 9.9405268 s
