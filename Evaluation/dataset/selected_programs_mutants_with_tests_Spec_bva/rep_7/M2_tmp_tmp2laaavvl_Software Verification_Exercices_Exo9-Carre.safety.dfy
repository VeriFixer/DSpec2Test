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

method {:test} Test11() {
var r0 := Carre(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 7.6891597 s
