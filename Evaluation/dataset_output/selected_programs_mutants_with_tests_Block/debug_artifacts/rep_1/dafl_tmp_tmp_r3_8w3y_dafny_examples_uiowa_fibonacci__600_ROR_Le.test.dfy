// dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_fibonacci.dfy

function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method {:testEntry} ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  if n == 0 {
    f := 0;
  } else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
    f := 1;
    while i <= n
      invariant i <= n
      invariant f_1 == fib(i - 1)
      invariant f == fib(i)
      decreases n - i
    {
      f_2 := f_1;
      f_1 := f;
      f := f_1 + f_2;
      i := i + 1;
    }
  }
}

method {:test} Test0() {
var r0 := ComputeFib(2);
expect r0 == fib(2);
}
method {:test} Test1() {
var r0 := ComputeFib(0);
expect r0 == fib(0);
}

// REPEAT 1 - TIME: 2.6749671 s
