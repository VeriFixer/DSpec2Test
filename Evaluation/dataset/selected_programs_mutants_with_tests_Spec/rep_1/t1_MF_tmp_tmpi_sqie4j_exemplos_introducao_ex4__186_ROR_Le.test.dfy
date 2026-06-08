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
  while i <= n
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

// REPEAT 1 - TIME: 2.8228443 s
