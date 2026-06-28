// t1_MF_tmp_tmpi_sqie4j_exemplos_introducao_ex4.dfy

function Fat(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}

method {:testEntry} Fatorial(n: nat) returns (r: nat)
  ensures r == Fat(n)
{
  r := 1;
  var i := 0;
  while false
    invariant 0 <= i <= n
    invariant r == Fat(i)
  {
    i := i + 1;
    r := r * i;
  }
}


method {:test} Test0() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}
method {:test} Test1() {
var r0 := Fatorial(100);
expect r0 == Fat(100);
}

// REPEAT 1 - TIME: 7.2196971 s

method {:test} Test6() {
var r0 := Fatorial(101);
expect r0 == Fat(101);
}

// REPEAT 2 - TIME: 8.3527946 s

method {:test} Test7() {
var r0 := Fatorial(102);
expect r0 == Fat(102);
}

// REPEAT 3 - TIME: 9.500842 s

method {:test} Test8() {
var r0 := Fatorial(103);
expect r0 == Fat(103);
}

// REPEAT 4 - TIME: 10.4388534 s

method {:test} Test9() {
var r0 := Fatorial(104);
expect r0 == Fat(104);
}

// REPEAT 5 - TIME: 11.3435637 s

method {:test} Test10() {
var r0 := Fatorial(105);
expect r0 == Fat(105);
}

// REPEAT 6 - TIME: 12.1564855 s

method {:test} Test11() {
var r0 := Fatorial(106);
expect r0 == Fat(106);
}

// REPEAT 7 - TIME: 13.1141503 s

method {:test} Test12() {
var r0 := Fatorial(107);
expect r0 == Fat(107);
}

// REPEAT 8 - TIME: 13.9207098 s

method {:test} Test13() {
var r0 := Fatorial(108);
expect r0 == Fat(108);
}

// REPEAT 9 - TIME: 14.7985283 s

method {:test} Test14() {
var r0 := Fatorial(109);
expect r0 == Fat(109);
}

// REPEAT 10 - TIME: 15.6165961 s
