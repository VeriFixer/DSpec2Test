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

method {:test} Test9() {
var r0 := Carre(10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 7.8767005 s
