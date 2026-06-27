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
  while i == n
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
var r0 := calcF(2);
expect r0 == F(2);
}

// REPEAT 1 - TIME: 3.0582948 s

method {:test} Test1() {
var r0 := calcF(1242);
expect r0 == F(1242);
}

// REPEAT 2 - TIME: 4.012166 s

method {:test} Test2() {
var r0 := calcF(1243);
expect r0 == F(1243);
}

// REPEAT 3 - TIME: 4.930509 s

method {:test} Test3() {
var r0 := calcF(1244);
expect r0 == F(1244);
}

// REPEAT 4 - TIME: 5.7947644 s

method {:test} Test4() {
var r0 := calcF(1245);
expect r0 == F(1245);
}

// REPEAT 5 - TIME: 6.8754305 s

method {:test} Test5() {
var r0 := calcF(1246);
expect r0 == F(1246);
}

// REPEAT 6 - TIME: 7.8364902 s

method {:test} Test6() {
var r0 := calcF(1247);
expect r0 == F(1247);
}

// REPEAT 7 - TIME: 8.6673265 s

method {:test} Test7() {
var r0 := calcF(1248);
expect r0 == F(1248);
}

// REPEAT 8 - TIME: 9.6103975 s

method {:test} Test8() {
var r0 := calcF(1249);
expect r0 == F(1249);
}

// REPEAT 9 - TIME: 10.2453415 s

method {:test} Test9() {
var r0 := calcF(1250);
expect r0 == F(1250);
}

// REPEAT 10 - TIME: 10.84011 s
