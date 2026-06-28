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
  while i > n
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

// REPEAT 1 - TIME: 11.5530916 s

method {:test} Test1() {
var r0 := calcF(1);
expect r0 == F(1);
}

// REPEAT 2 - TIME: 18.1469061 s

method {:test} Test2() {
var r0 := calcF(2);
expect r0 == F(2);
}

// REPEAT 3 - TIME: 24.0095483 s

method {:test} Test3() {
var r0 := calcF(3);
expect r0 == F(3);
}

// REPEAT 4 - TIME: 29.9657778 s

method {:test} Test4() {
var r0 := calcF(980);
expect r0 == F(980);
}

// REPEAT 5 - TIME: 35.9871785 s

method {:test} Test5() {
var r0 := calcF(981);
expect r0 == F(981);
}

// REPEAT 6 - TIME: 41.9609001 s

method {:test} Test6() {
var r0 := calcF(982);
expect r0 == F(982);
}

// REPEAT 7 - TIME: 47.37968 s

method {:test} Test7() {
var r0 := calcF(983);
expect r0 == F(983);
}

// REPEAT 8 - TIME: 52.9595755 s

method {:test} Test8() {
var r0 := calcF(984);
expect r0 == F(984);
}

// REPEAT 9 - TIME: 60.4481875 s

method {:test} Test9() {
var r0 := calcF(985);
expect r0 == F(985);
}

// REPEAT 10 - TIME: 68.5840407 s
