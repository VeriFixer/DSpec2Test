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

method {:test} Test2() {
var r0 := Carre(3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 3.4436798 s
