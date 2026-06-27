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

// REPEAT 1 - TIME: 4.0564372 s

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

// REPEAT 2 - TIME: 6.6394597 s

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
var r0 := A1(2, -1262);
expect r0 == 2 + -1262;
}

// REPEAT 3 - TIME: 9.166181 s

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
var r0 := A1(3, -804);
expect r0 == 3 + -804;
}

// REPEAT 4 - TIME: 11.7112285 s

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
var r0 := A1(4, -234);
expect r0 == 4 + -234;
}

// REPEAT 5 - TIME: 13.5975179 s

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
var r0 := A1(5, -36);
expect r0 == 5 + -36;
}

// REPEAT 6 - TIME: 15.4230986 s

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
var r0 := A1(6, -20);
expect r0 == 6 + -20;
}

// REPEAT 7 - TIME: 17.4194534 s

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
var r0 := A1(7, -12);
expect r0 == 7 + -12;
}

// REPEAT 8 - TIME: 19.7319087 s

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

// REPEAT 9 - TIME: 22.0507724 s

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

// REPEAT 10 - TIME: 23.9165187 s
