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

method {:test} Test13() {
var r0 := Carre(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 8.5107903 s
