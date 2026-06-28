// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube.dfy

method {:testEntry} Cube(n: nat) returns (c: nat)
  ensures c == n * n * n
{
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while true
    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := Cube(1797);
expect r0 == 1797 * 1797 * 1797;
}

// REPEAT 1 - TIME: 2.0296107 s

method {:test} Test1() {
var r0 := Cube(9517);
expect r0 == 9517 * 9517 * 9517;
}

// REPEAT 2 - TIME: 2.87859 s

method {:test} Test2() {
var r0 := Cube(17237);
expect r0 == 17237 * 17237 * 17237;
}

// REPEAT 3 - TIME: 3.5317855 s

method {:test} Test3() {
var r0 := Cube(17238);
expect r0 == 17238 * 17238 * 17238;
}

// REPEAT 4 - TIME: 4.2207319 s

method {:test} Test4() {
var r0 := Cube(24958);
expect r0 == 24958 * 24958 * 24958;
}

// REPEAT 5 - TIME: 4.8140572 s

method {:test} Test5() {
var r0 := Cube(32678);
expect r0 == 32678 * 32678 * 32678;
}

// REPEAT 6 - TIME: 5.3859274 s

method {:test} Test6() {
var r0 := Cube(32679);
expect r0 == 32679 * 32679 * 32679;
}

// REPEAT 7 - TIME: 6.0300236 s

method {:test} Test7() {
var r0 := Cube(32680);
expect r0 == 32680 * 32680 * 32680;
}

// REPEAT 8 - TIME: 6.5579961 s

method {:test} Test8() {
var r0 := Cube(32681);
expect r0 == 32681 * 32681 * 32681;
}

// REPEAT 9 - TIME: 7.0870541 s

method {:test} Test9() {
var r0 := Cube(40401);
expect r0 == 40401 * 40401 * 40401;
}

// REPEAT 10 - TIME: 7.8325091 s
