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
  while false
    invariant 1 <= i <= n + 1
    invariant f == Fat(i - 1)
    decreases n - i
  {
    f := f * i;
    i := i + 1;
  }
  return f;
}

method {:test} Test0() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}

// REPEAT 1 - TIME: 6.8234469 s
