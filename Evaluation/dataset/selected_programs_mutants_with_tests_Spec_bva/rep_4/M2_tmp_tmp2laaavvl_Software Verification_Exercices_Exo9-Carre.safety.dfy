method {:testEntry} Carre(a: nat) returns (c: nat)
ensures c == a*a
{
    var i := 0;
    c := 0;
    while i != a
    invariant 0 <= i <= a
    invariant c == i*i
    decreases a - i
  {
    c := c + 2*i +1;
    i := i + 1;
  }
}

method {:test} Test8() {
var r0 := Carre(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 6.1333465 s
