// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy

method {:testEntry} Carre(a: nat) returns (c: nat)
  ensures c == a * a
{
  var i := 0;
  c := 0;
  while i <= a
    invariant 0 <= i <= a
    invariant c == i * i
    decreases a - i
  {
    c := c + 2 * i + 1;
    i := i + 1;
  }
}


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

// REPEAT 1 - TIME: 2.7341075 s

method {:test} Test1() {
var r0 := Carre(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.7131042 s

method {:test} Test2() {
var r0 := Carre(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 4.7485198 s

method {:test} Test3() {
var r0 := Carre(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 5.6973662 s

method {:test} Test4() {
var r0 := Carre(4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 6.4201802 s

method {:test} Test5() {
var r0 := Carre(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 7.2589416 s

method {:test} Test6() {
var r0 := Carre(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 8.0472803 s

method {:test} Test7() {
var r0 := Carre(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 8.9322977 s

method {:test} Test8() {
var r0 := Carre(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 9.6705845 s

method {:test} Test9() {
var r0 := Carre(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 10.347136 s
