// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_fatorial2.dfy

function Fat(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}

method {:testEntry} Fatorial(n: nat) returns (f: nat)
  ensures f == Fat(n)
{
  f := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant f == Fat(i - 1)
    decreases n - i
  {
    f := f + i;
    i := i + 1;
  }
  return f;
}


method {:test} Test0() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}

// REPEAT 1 - TIME: 2.4893292 s

method {:test} Test1() {
var r0 := Fatorial(3);
expect r0 == Fat(3);
}

// REPEAT 2 - TIME: 3.4445682 s

method {:test} Test2() {
var r0 := Fatorial(4);
expect r0 == Fat(4);
}

// REPEAT 3 - TIME: 4.605401 s

method {:test} Test3() {
var r0 := Fatorial(5);
expect r0 == Fat(5);
}

// REPEAT 4 - TIME: 5.748603 s

method {:test} Test4() {
var r0 := Fatorial(6);
expect r0 == Fat(6);
}

// REPEAT 5 - TIME: 6.9812224 s

method {:test} Test5() {
var r0 := Fatorial(7);
expect r0 == Fat(7);
}

// REPEAT 6 - TIME: 7.9528787 s

method {:test} Test6() {
var r0 := Fatorial(8);
expect r0 == Fat(8);
}

// REPEAT 7 - TIME: 8.8722637 s

method {:test} Test7() {
var r0 := Fatorial(9);
expect r0 == Fat(9);
}

// REPEAT 8 - TIME: 9.6565944 s

method {:test} Test8() {
var r0 := Fatorial(1152);
expect r0 == Fat(1152);
}

// REPEAT 9 - TIME: 10.3531235 s

method {:test} Test9() {
var r0 := Fatorial(1153);
expect r0 == Fat(1153);
}

// REPEAT 10 - TIME: 11.0790796 s
