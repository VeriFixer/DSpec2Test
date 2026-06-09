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

method {:test} Test0() {
var r0 := Carre(0);
expect r0 == 0 * 0;
}
method {:test} Test1() {
var r0 := Carre(100);
expect r0 == 100 * 100;
}
method {:test} Test3() {
var r0 := Carre(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 5.1192996 s
