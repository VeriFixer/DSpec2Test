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

method {:test} Test6() {
var r0 := Carre(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 27.3401392 s
