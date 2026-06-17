// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim.dfy

ghost function gcd(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x == y then
    x
  else if x > y then
    gcd(x - y, y)
  else
    gcd(x, y - x)
}

method {:testEntry} gcdI(m: int, n: int) returns (d: int)
  requires m > 0 && n > 0
  ensures d == gcd(m, n)
{
  var x: int;
  d := m;
  x := n;
  while d == x
    invariant x > 0
    invariant d > 0
    invariant gcd(d, x) == gcd(m, n)
    decreases x + d
  {
    if d > x {
      d := d - x;
    } else {
      x := x - d;
    }
  }
}

ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases if x > y then x else y
{
  if x == y then
    x
  else if x > y then
    gcd'(x - y, y)
  else
    gcd(y, x)
}



//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

method {:testEntry} gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
{
    var x: int;
    d := m;
    x := n;
    while (d != x)
    invariant x > 0;
    invariant d > 0;
    invariant gcd(d, x) == gcd(m, n);
    decreases x+d;
    {
        if (d > x)
        {
            d := d - x;
        }
        else
        {
            x := x - d;
        }
    }
}

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}

method {:test} Test0() {
expect 2 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(2, 1);
}

// REPEAT 1 - TIME: 9.7402268 s

method {:test} Test1() {
expect 7724 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7724, 2);
}

// REPEAT 2 - TIME: 14.6579087 s

method {:test} Test2() {
expect 7725 > 0 && 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7725, 3);
}

// REPEAT 3 - TIME: 19.2302004 s

method {:test} Test3() {
expect 23164 > 0 && 11582 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23164, 11582);
}

// REPEAT 4 - TIME: 24.6641977 s

method {:test} Test4() {
expect 30886 > 0 && 11583 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30886, 11583);
}

// REPEAT 5 - TIME: 29.1933433 s

method {:test} Test5() {
expect 30887 > 0 && 11584 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30887, 11584);
}

// REPEAT 6 - TIME: 34.902056 s

method {:test} Test6() {
expect 30888 > 0 && 11585 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30888, 11585);
}

// REPEAT 7 - TIME: 40.4290621 s

method {:test} Test7() {
expect 30889 > 0 && 11586 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30889, 11586);
}

// REPEAT 8 - TIME: 46.3484551 s

method {:test} Test8() {
expect 46328 > 0 && 23164 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46328, 23164);
}

// REPEAT 9 - TIME: 51.9637859 s

method {:test} Test9() {
expect 46330 > 0 && 23165 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46330, 23165);
}

// REPEAT 10 - TIME: 57.6469103 s
