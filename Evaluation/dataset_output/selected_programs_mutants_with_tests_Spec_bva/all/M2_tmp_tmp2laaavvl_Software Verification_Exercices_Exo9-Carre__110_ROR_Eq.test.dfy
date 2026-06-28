// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy

method {:testEntry} Carre(a: nat) returns (c: nat)
  ensures c == a * a
{
  var i := 0;
  c := 0;
  while i == a
    invariant 0 <= i <= a
    invariant c == i * i
    decreases a - i
  {
    c := c + 2 * i + 1;
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

// REPEAT 1 - TIME: 8.5308252 s

method {:test} Test6() {
var r0 := Carre(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 9.6744732 s

method {:test} Test7() {
var r0 := Carre(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 10.5597287 s

method {:test} Test8() {
var r0 := Carre(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 11.4236448 s

method {:test} Test9() {
var r0 := Carre(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 12.2143457 s

method {:test} Test10() {
var r0 := Carre(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 13.216005 s

method {:test} Test11() {
var r0 := Carre(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 14.1802881 s

method {:test} Test12() {
var r0 := Carre(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 15.097225 s

method {:test} Test13() {
var r0 := Carre(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 16.1951808 s

method {:test} Test14() {
var r0 := Carre(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 17.1451726 s
