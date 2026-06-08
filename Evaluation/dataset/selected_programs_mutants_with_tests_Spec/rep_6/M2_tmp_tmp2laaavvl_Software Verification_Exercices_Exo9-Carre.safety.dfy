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

method {:test} Test5() {
var r0 := Carre(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 8.0497975 s
