// cs357_tmp_tmpn4fsvwzs_lab7_question5.dfy

method {:testEntry} M1(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x >= 0 {
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
var r0 := M1(1, 7719);
expect r0 == 1 * 7719;
}
method {:test} Test1() {
var r0 := M1(-1, 8365);
expect r0 == -1 * 8365;
}
method {:test} Test2() {
var r0 := M1(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test3() {
var r0 := A1(-1236, 3675);
expect r0 == -1236 + 3675;
}
method {:test} Test5() {
var r0 := A1(0, -1);
expect r0 == 0 + -1;
}

// REPEAT 1 - TIME: 4.2837866 s

method {:test} Test6() {
var r0 := M1(2, 8366);
expect r0 == 2 * 8366;
}
method {:test} Test7() {
var r0 := M1(-2, 8366);
expect r0 == -2 * 8366;
}
method {:test} Test9() {
var r0 := A1(1, 3676);
expect r0 == 1 + 3676;
}
method {:test} Test11() {
var r0 := A1(1, -1798);
expect r0 == 1 + -1798;
}

// REPEAT 2 - TIME: 7.4614835 s

method {:test} Test12() {
var r0 := M1(3, 8367);
expect r0 == 3 * 8367;
}
method {:test} Test13() {
var r0 := M1(-3, 8367);
expect r0 == -3 * 8367;
}
method {:test} Test15() {
var r0 := A1(2, 3677);
expect r0 == 2 + 3677;
}
method {:test} Test17() {
var r0 := A1(2, -126);
expect r0 == 2 + -126;
}

// REPEAT 3 - TIME: 9.7180627 s

method {:test} Test18() {
var r0 := M1(4, 8368);
expect r0 == 4 * 8368;
}
method {:test} Test19() {
var r0 := M1(-4, 8368);
expect r0 == -4 * 8368;
}
method {:test} Test21() {
var r0 := A1(3, 3678);
expect r0 == 3 + 3678;
}
method {:test} Test23() {
var r0 := A1(3, -108);
expect r0 == 3 + -108;
}

// REPEAT 4 - TIME: 11.7333815 s

method {:test} Test24() {
var r0 := M1(5, 8369);
expect r0 == 5 * 8369;
}
method {:test} Test25() {
var r0 := M1(-5, 8369);
expect r0 == -5 * 8369;
}
method {:test} Test27() {
var r0 := A1(4, 3679);
expect r0 == 4 + 3679;
}
method {:test} Test29() {
var r0 := A1(4, -76);
expect r0 == 4 + -76;
}

// REPEAT 5 - TIME: 13.6703257 s

method {:test} Test30() {
var r0 := M1(6, 8370);
expect r0 == 6 * 8370;
}
method {:test} Test31() {
var r0 := M1(-6, 8370);
expect r0 == -6 * 8370;
}
method {:test} Test33() {
var r0 := A1(5, 3680);
expect r0 == 5 + 3680;
}
method {:test} Test35() {
var r0 := A1(5, -44);
expect r0 == 5 + -44;
}

// REPEAT 6 - TIME: 16.1979188 s

method {:test} Test36() {
var r0 := M1(7, 8371);
expect r0 == 7 * 8371;
}
method {:test} Test37() {
var r0 := M1(-7, 8371);
expect r0 == -7 * 8371;
}
method {:test} Test39() {
var r0 := A1(6, 3681);
expect r0 == 6 + 3681;
}
method {:test} Test41() {
var r0 := A1(6, -6);
expect r0 == 6 + -6;
}

// REPEAT 7 - TIME: 18.451852 s

method {:test} Test42() {
var r0 := M1(8, 8372);
expect r0 == 8 * 8372;
}
method {:test} Test43() {
var r0 := M1(-8, 8372);
expect r0 == -8 * 8372;
}
method {:test} Test45() {
var r0 := A1(7, 3682);
expect r0 == 7 + 3682;
}
method {:test} Test47() {
var r0 := A1(7, -4);
expect r0 == 7 + -4;
}

// REPEAT 8 - TIME: 20.4163997 s

method {:test} Test48() {
var r0 := M1(9, 8373);
expect r0 == 9 * 8373;
}
method {:test} Test49() {
var r0 := M1(-9, 8373);
expect r0 == -9 * 8373;
}
method {:test} Test51() {
var r0 := A1(8, 3683);
expect r0 == 8 + 3683;
}
method {:test} Test53() {
var r0 := A1(8, -2);
expect r0 == 8 + -2;
}

// REPEAT 9 - TIME: 22.3426976 s

method {:test} Test54() {
var r0 := M1(10, 8374);
expect r0 == 10 * 8374;
}
method {:test} Test55() {
var r0 := M1(-10, 8374);
expect r0 == -10 * 8374;
}
method {:test} Test57() {
var r0 := A1(9, 3684);
expect r0 == 9 + 3684;
}
method {:test} Test59() {
var r0 := A1(9, -3);
expect r0 == 9 + -3;
}

// REPEAT 10 - TIME: 24.0679746 s
