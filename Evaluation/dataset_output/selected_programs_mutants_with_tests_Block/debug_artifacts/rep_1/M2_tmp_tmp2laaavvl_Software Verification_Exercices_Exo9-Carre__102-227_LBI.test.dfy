// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy

method {:testEntry} Carre(a: nat) returns (c: nat)
  ensures c == a * a
{
  var i := 0;
  c := 0;
  while i != a
    invariant 0 <= i <= a
    invariant c == i * i
    decreases a - i
  {
    break;
    c := c + 2 * i + 1;
    i := i + 1;
  }
}

method {:test} Test0() {
var r0 := Carre(1);
expect r0 == 1 * 1;
}

// REPEAT 1 - TIME: 1.9179265 s
