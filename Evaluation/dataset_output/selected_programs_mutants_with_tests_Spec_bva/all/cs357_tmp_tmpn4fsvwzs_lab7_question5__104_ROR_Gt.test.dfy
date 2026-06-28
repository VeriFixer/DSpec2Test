// cs357_tmp_tmpn4fsvwzs_lab7_question5.dfy

method {:testEntry} M1(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x > 0 {
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
var r0 := M1(7719, 0);
expect r0 == 7719 * 0;
}
method {:test} Test1() {
var r0 := M1(-100, 0);
expect r0 == -100 * 0;
}
method {:test} Test2() {
var r0 := M1(100, 0);
expect r0 == 100 * 0;
}
method {:test} Test3() {
var r0 := M1(0, -100);
expect r0 == 0 * -100;
}
method {:test} Test4() {
var r0 := M1(0, 100);
expect r0 == 0 * 100;
}
method {:test} Test6() {
var r0 := M1(-100, 1);
expect r0 == -100 * 1;
}
method {:test} Test7() {
var r0 := M1(100, 1);
expect r0 == 100 * 1;
}
method {:test} Test10() {
var r0 := A1(0, 0);
expect r0 == 0 + 0;
}
method {:test} Test11() {
var r0 := A1(-100, 100);
expect r0 == -100 + 100;
}
method {:test} Test12() {
var r0 := A1(100, -100);
expect r0 == 100 + -100;
}
method {:test} Test16() {
var r0 := A1(-100, 0);
expect r0 == -100 + 0;
}
method {:test} Test17() {
var r0 := A1(100, 0);
expect r0 == 100 + 0;
}

// REPEAT 1 - TIME: 13.4374539 s

method {:test} Test20() {
var r0 := M1(7720, 101);
expect r0 == 7720 * 101;
}
method {:test} Test21() {
var r0 := A1(101, 101);
expect r0 == 101 + 101;
}

// REPEAT 2 - TIME: 14.8029552 s

method {:test} Test22() {
var r0 := M1(7721, 102);
expect r0 == 7721 * 102;
}
method {:test} Test23() {
var r0 := A1(102, 102);
expect r0 == 102 + 102;
}

// REPEAT 3 - TIME: 16.081464 s

method {:test} Test24() {
var r0 := M1(7722, 103);
expect r0 == 7722 * 103;
}
method {:test} Test25() {
var r0 := A1(103, 103);
expect r0 == 103 + 103;
}

// REPEAT 4 - TIME: 16.9801319 s

method {:test} Test26() {
var r0 := M1(7723, 104);
expect r0 == 7723 * 104;
}
method {:test} Test27() {
var r0 := A1(104, 104);
expect r0 == 104 + 104;
}

// REPEAT 5 - TIME: 18.1918094 s

method {:test} Test28() {
var r0 := M1(7724, 105);
expect r0 == 7724 * 105;
}
method {:test} Test29() {
var r0 := A1(105, 105);
expect r0 == 105 + 105;
}

// REPEAT 6 - TIME: 19.234449 s

method {:test} Test30() {
var r0 := M1(7725, 106);
expect r0 == 7725 * 106;
}
method {:test} Test31() {
var r0 := A1(106, 106);
expect r0 == 106 + 106;
}

// REPEAT 7 - TIME: 20.2994412 s

method {:test} Test32() {
var r0 := M1(7726, 107);
expect r0 == 7726 * 107;
}
method {:test} Test33() {
var r0 := A1(107, 107);
expect r0 == 107 + 107;
}

// REPEAT 8 - TIME: 21.1654894 s

method {:test} Test34() {
var r0 := M1(7727, 108);
expect r0 == 7727 * 108;
}
method {:test} Test35() {
var r0 := A1(108, 108);
expect r0 == 108 + 108;
}

// REPEAT 9 - TIME: 22.2935283 s

method {:test} Test36() {
var r0 := M1(7728, 109);
expect r0 == 7728 * 109;
}
method {:test} Test37() {
var r0 := A1(109, 109);
expect r0 == 109 + 109;
}

// REPEAT 10 - TIME: 23.5046653 s
