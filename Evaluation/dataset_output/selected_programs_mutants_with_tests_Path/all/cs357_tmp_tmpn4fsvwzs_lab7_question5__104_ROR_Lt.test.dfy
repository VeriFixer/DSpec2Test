// cs357_tmp_tmpn4fsvwzs_lab7_question5.dfy

method {:testEntry} M1(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x < 0 {
    r := 0;
  } else if x < 0 {
    r := M1(-x, y);
    r := -r;
  } else {
    r := M1(x - 1, y);
    r := A1(r, y);
  }
}

method {:testEntry} A1(x: int, y: int) returns (r: int)
  ensures r == x + y
{
  r := x;
  if y < 0 {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant -n >= 0
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant n >= 0
    {
      r := r + 1;
      n := n - 1;
    }
  }
}


method {:test} Test0() {
var r0 := M1(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test1() {
var r0 := M1(-1, 0);
expect r0 == -1 * 0;
}
method {:test} Test2() {
var r0 := M1(1, 7719);
expect r0 == 1 * 7719;
}
method {:test} Test3() {
var r0 := A1(1, -1);
expect r0 == 1 + -1;
}
method {:test} Test4() {
var r0 := A1(-1, 1);
expect r0 == -1 + 1;
}

// REPEAT 1 - TIME: 7.886683 s

method {:test} Test5() {
var r0 := M1(-2, 7720);
expect r0 == -2 * 7720;
}
method {:test} Test6() {
var r0 := M1(2, 7720);
expect r0 == 2 * 7720;
}
method {:test} Test7() {
var r0 := A1(2, -2);
expect r0 == 2 + -2;
}
method {:test} Test8() {
var r0 := A1(2, 2);
expect r0 == 2 + 2;
}

// REPEAT 2 - TIME: 13.4170056 s

method {:test} Test9() {
var r0 := M1(-3, 7721);
expect r0 == -3 * 7721;
}
method {:test} Test10() {
var r0 := M1(7722, 7721);
expect r0 == 7722 * 7721;
}
method {:test} Test11() {
var r0 := A1(1239, -1239);
expect r0 == 1239 + -1239;
}
method {:test} Test12() {
var r0 := A1(3, 1239);
expect r0 == 3 + 1239;
}

// REPEAT 3 - TIME: 18.2079419 s

method {:test} Test13() {
var r0 := M1(-4, 7722);
expect r0 == -4 * 7722;
}
method {:test} Test14() {
var r0 := M1(7723, 7722);
expect r0 == 7723 * 7722;
}
method {:test} Test15() {
var r0 := A1(1240, -1012);
expect r0 == 1240 + -1012;
}
method {:test} Test16() {
var r0 := A1(1240, 1240);
expect r0 == 1240 + 1240;
}

// REPEAT 4 - TIME: 23.6283201 s

method {:test} Test17() {
var r0 := M1(-5, 7723);
expect r0 == -5 * 7723;
}
method {:test} Test18() {
var r0 := M1(7724, 7723);
expect r0 == 7724 * 7723;
}
method {:test} Test19() {
var r0 := A1(1241, -962);
expect r0 == 1241 + -962;
}
method {:test} Test20() {
var r0 := A1(1241, 1241);
expect r0 == 1241 + 1241;
}

// REPEAT 5 - TIME: 29.3077953 s

method {:test} Test21() {
var r0 := M1(-6, 7724);
expect r0 == -6 * 7724;
}
method {:test} Test22() {
var r0 := M1(7725, 7724);
expect r0 == 7725 * 7724;
}
method {:test} Test23() {
var r0 := A1(1242, -821);
expect r0 == 1242 + -821;
}
method {:test} Test24() {
var r0 := A1(1242, 1242);
expect r0 == 1242 + 1242;
}

// REPEAT 6 - TIME: 35.7248386 s

method {:test} Test25() {
var r0 := M1(-7, 7725);
expect r0 == -7 * 7725;
}
method {:test} Test26() {
var r0 := M1(7726, 7725);
expect r0 == 7726 * 7725;
}
method {:test} Test27() {
var r0 := A1(1243, -32);
expect r0 == 1243 + -32;
}
method {:test} Test28() {
var r0 := A1(1243, 1243);
expect r0 == 1243 + 1243;
}

// REPEAT 7 - TIME: 44.2715688 s

method {:test} Test29() {
var r0 := M1(-8, 7726);
expect r0 == -8 * 7726;
}
method {:test} Test30() {
var r0 := M1(7727, 7726);
expect r0 == 7727 * 7726;
}
method {:test} Test31() {
var r0 := A1(1244, -21);
expect r0 == 1244 + -21;
}
method {:test} Test32() {
var r0 := A1(1244, 1244);
expect r0 == 1244 + 1244;
}

// REPEAT 8 - TIME: 50.1740497 s

method {:test} Test33() {
var r0 := M1(-9, 7727);
expect r0 == -9 * 7727;
}
method {:test} Test34() {
var r0 := M1(7728, 7727);
expect r0 == 7728 * 7727;
}
method {:test} Test35() {
var r0 := A1(1245, -4);
expect r0 == 1245 + -4;
}
method {:test} Test36() {
var r0 := A1(1245, 1245);
expect r0 == 1245 + 1245;
}

// REPEAT 9 - TIME: 58.2953827 s

method {:test} Test37() {
var r0 := M1(-10, 7728);
expect r0 == -10 * 7728;
}
method {:test} Test38() {
var r0 := M1(7729, 7728);
expect r0 == 7729 * 7728;
}
method {:test} Test39() {
var r0 := A1(1246, -3);
expect r0 == 1246 + -3;
}
method {:test} Test40() {
var r0 := A1(1246, 1246);
expect r0 == 1246 + 1246;
}

// REPEAT 10 - TIME: 66.9533382 s
