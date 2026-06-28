// cs357_tmp_tmpn4fsvwzs_lab7_question5.dfy

method {:testEntry} M1(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x == 0 {
    r := 0;
  } else if x != 0 {
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
var r0 := A1(0, 0);
expect r0 == 0 + 0;
}

// REPEAT 1 - TIME: 3.5677452 s

method {:test} Test2() {
var r0 := M1(7720, 1);
expect r0 == 7720 * 1;
}
method {:test} Test3() {
var r0 := A1(1, 1);
expect r0 == 1 + 1;
}

// REPEAT 2 - TIME: 4.9270004 s

method {:test} Test4() {
var r0 := M1(7721, 7721);
expect r0 == 7721 * 7721;
}
method {:test} Test5() {
var r0 := A1(2, 2);
expect r0 == 2 + 2;
}

// REPEAT 3 - TIME: 6.2287413 s

method {:test} Test6() {
var r0 := M1(7722, 7722);
expect r0 == 7722 * 7722;
}
method {:test} Test7() {
var r0 := A1(3, 3);
expect r0 == 3 + 3;
}

// REPEAT 4 - TIME: 7.4628105 s

method {:test} Test8() {
var r0 := M1(7723, 7723);
expect r0 == 7723 * 7723;
}
method {:test} Test9() {
var r0 := A1(4, 4);
expect r0 == 4 + 4;
}

// REPEAT 5 - TIME: 8.5323524 s

method {:test} Test10() {
var r0 := M1(7724, 7724);
expect r0 == 7724 * 7724;
}
method {:test} Test11() {
var r0 := A1(5, 5);
expect r0 == 5 + 5;
}

// REPEAT 6 - TIME: 9.5012809 s

method {:test} Test12() {
var r0 := M1(7725, 7725);
expect r0 == 7725 * 7725;
}
method {:test} Test13() {
var r0 := A1(6, 6);
expect r0 == 6 + 6;
}

// REPEAT 7 - TIME: 10.810067 s

method {:test} Test14() {
var r0 := M1(7726, 7726);
expect r0 == 7726 * 7726;
}
method {:test} Test15() {
var r0 := A1(7, 7);
expect r0 == 7 + 7;
}

// REPEAT 8 - TIME: 11.771159 s

method {:test} Test16() {
var r0 := M1(7727, 7727);
expect r0 == 7727 * 7727;
}
method {:test} Test17() {
var r0 := A1(8, 8);
expect r0 == 8 + 8;
}

// REPEAT 9 - TIME: 12.8067 s

method {:test} Test18() {
var r0 := M1(7728, 7728);
expect r0 == 7728 * 7728;
}
method {:test} Test19() {
var r0 := A1(9, 9);
expect r0 == 9 + 9;
}

// REPEAT 10 - TIME: 13.966037 s
