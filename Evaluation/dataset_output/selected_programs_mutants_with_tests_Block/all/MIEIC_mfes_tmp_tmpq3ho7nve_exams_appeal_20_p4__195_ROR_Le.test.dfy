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

// REPEAT 1 - TIME: 2.3444576 s

method {:test} Test1() {
var r0 := calcF(8951);
expect r0 == F(8951);
}

// REPEAT 2 - TIME: 3.3818267 s

method {:test} Test2() {
var r0 := calcF(8952);
expect r0 == F(8952);
}

// REPEAT 3 - TIME: 4.3387687 s

method {:test} Test3() {
var r0 := calcF(8953);
expect r0 == F(8953);
}

// REPEAT 4 - TIME: 5.3484481 s

method {:test} Test4() {
var r0 := calcF(8954);
expect r0 == F(8954);
}

// REPEAT 5 - TIME: 6.3938129 s

method {:test} Test5() {
var r0 := calcF(8955);
expect r0 == F(8955);
}

// REPEAT 6 - TIME: 7.3185802 s

method {:test} Test6() {
var r0 := calcF(8956);
expect r0 == F(8956);
}

// REPEAT 7 - TIME: 8.2296946 s

method {:test} Test7() {
var r0 := calcF(8957);
expect r0 == F(8957);
}

// REPEAT 8 - TIME: 9.1930677 s

method {:test} Test8() {
var r0 := calcF(8958);
expect r0 == F(8958);
}

// REPEAT 9 - TIME: 10.0345182 s

method {:test} Test9() {
var r0 := calcF(8959);
expect r0 == F(8959);
}

// REPEAT 10 - TIME: 10.771825 s
