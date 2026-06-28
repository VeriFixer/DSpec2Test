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
  while true
    invariant 0 <= i <= n
    invariant r == Fat(i)
  {
    i := i + 1;
    r := r * i;
  }
}


method {:test} Test0() {
var r0 := Fatorial(1);
expect r0 == Fat(1);
}

// REPEAT 1 - TIME: 2.3516584 s

method {:test} Test1() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}

// REPEAT 2 - TIME: 3.3712328 s

method {:test} Test2() {
var r0 := Fatorial(3);
expect r0 == Fat(3);
}

// REPEAT 3 - TIME: 3.9632874 s

method {:test} Test3() {
var r0 := Fatorial(4);
expect r0 == Fat(4);
}

// REPEAT 4 - TIME: 4.6205575 s

method {:test} Test4() {
var r0 := Fatorial(5);
expect r0 == Fat(5);
}

// REPEAT 5 - TIME: 5.2772216 s

method {:test} Test5() {
var r0 := Fatorial(6);
expect r0 == Fat(6);
}

// REPEAT 6 - TIME: 5.964874 s

method {:test} Test6() {
var r0 := Fatorial(7);
expect r0 == Fat(7);
}

// REPEAT 7 - TIME: 6.5185384 s

method {:test} Test7() {
var r0 := Fatorial(8);
expect r0 == Fat(8);
}

// REPEAT 8 - TIME: 7.0503617 s

method {:test} Test8() {
var r0 := Fatorial(9);
expect r0 == Fat(9);
}

// REPEAT 9 - TIME: 7.5170099 s

method {:test} Test9() {
var r0 := Fatorial(10);
expect r0 == Fat(10);
}

// REPEAT 10 - TIME: 7.9537391 s
