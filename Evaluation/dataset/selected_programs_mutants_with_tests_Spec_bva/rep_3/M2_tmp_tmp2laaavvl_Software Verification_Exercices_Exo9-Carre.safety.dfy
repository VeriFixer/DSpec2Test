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

method {:test} Test7() {
var r0 := Carre(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 6.6069838 s
