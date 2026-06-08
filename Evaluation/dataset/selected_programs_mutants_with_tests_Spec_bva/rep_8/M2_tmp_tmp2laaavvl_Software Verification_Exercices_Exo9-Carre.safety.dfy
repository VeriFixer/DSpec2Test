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

method {:test} Test12() {
var r0 := Carre(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 8.0815533 s
